use core::ptr::{self, Shared};
use core::marker::Unsize;
#[cfg(target_has_atomic = "ptr")]
use core::sync::atomic::Ordering;

use BufferFullError;
use ring_buffer::RingBuffer;

impl<T, A> RingBuffer<T, A>
where
    A: Unsize<[T]>,
{
    /// Splits a statically allocated ring buffer into producer and consumer end points
    ///
    /// **Warning** the current single producer single consumer implementation only supports
    /// multi-core systems where `cfg(target_has_atomic = "ptr")` holds for all the cores. For
    /// example, a dual core system where one core is Cortex-M0 core and the other is Cortex-M3 core
    /// is not supported because Cortex-M0 (`thumbv6m-none-eabi`) doesn't satisfy
    /// `cfg(target_has_atomic = "ptr")`. All single core systems are supported.
    pub fn split(&'static mut self) -> (Producer<T, A>, Consumer<T, A>) {
        (
            Producer {
                rb: unsafe { Shared::new_unchecked(self) },
            },
            Consumer {
                rb: unsafe { Shared::new_unchecked(self) },
            },
        )
    }
}

/// A ring buffer "consumer"; it can dequeue items from the ring buffer
// NOTE the consumer semantically owns the `head` pointer of the ring buffer
pub struct Consumer<T, A>
where
    A: Unsize<[T]>,
{
    // XXX do we need to use `Shared` (for soundness) here?
    rb: Shared<RingBuffer<T, A>>,
}

impl<T, A> Consumer<T, A>
where
    A: Unsize<[T]>,
{
    /// Returns the item in the front of the queue, or `None` if the queue is empty
    #[cfg(target_has_atomic = "ptr")]
    pub fn dequeue(&mut self) -> Option<T> {
        let rb = unsafe { self.rb.as_ref() };

        let tail = rb.tail.load(Ordering::Relaxed);
        let head = rb.head.load(Ordering::Acquire);

        let n = rb.capacity() + 1;
        let buffer: &[T] = unsafe { rb.buffer.as_ref() };

        if head != tail {
            let item = unsafe { ptr::read(buffer.get_unchecked(head)) };
            rb.head.store((head + 1) % n, Ordering::Release);
            Some(item)
        } else {
            None
        }
    }

    /// Returns the item in the front of the queue, or `None` if the queue is empty
    #[cfg(not(target_has_atomic = "ptr"))]
    pub fn dequeue(&mut self) -> Option<T> {
        let rb = unsafe { self.rb.as_mut() };

        let n = rb.capacity() + 1;
        let buffer: &[T] = unsafe { rb.buffer.as_ref() };

        // NOTE(volatile) the value of `tail` can change at any time in the execution context of the
        // consumer so we inform this to the compiler using a volatile load
        if rb.head != unsafe { ptr::read_volatile(&rb.tail) } {
            let item = unsafe { ptr::read(buffer.get_unchecked(rb.head)) };
            rb.head = (rb.head + 1) % n;
            Some(item)
        } else {
            None
        }
    }
}

unsafe impl<T, A> Send for Consumer<T, A>
where
    A: Unsize<[T]>,
    T: Send,
{
}

/// A ring buffer "producer"; it can enqueue items into the ring buffer
// NOTE the producer semantically owns the `tail` pointer of the ring buffer
pub struct Producer<T, A>
where
    A: Unsize<[T]>,
{
    // XXX do we need to use `Shared` (for soundness) here?
    rb: Shared<RingBuffer<T, A>>,
}

impl<T, A> Producer<T, A>
where
    A: Unsize<[T]>,
{
    /// Adds an `item` to the end of the queue
    ///
    /// Returns `BufferFullError` if the queue is full
    #[cfg(target_has_atomic = "ptr")]
    pub fn enqueue(&mut self, item: T) -> Result<(), BufferFullError> {
        let rb = unsafe { self.rb.as_mut() };

        let head = rb.head.load(Ordering::Relaxed);
        let tail = rb.tail.load(Ordering::Acquire);

        let n = rb.capacity() + 1;
        let next_tail = (tail + 1) % n;

        let buffer: &mut [T] = unsafe { rb.buffer.as_mut() };

        if next_tail != head {
            // NOTE(ptr::write) the memory slot that we are about to write to is uninitialized. We
            // use `ptr::write` to avoid running `T`'s destructor on the uninitialized memory
            unsafe { ptr::write(buffer.get_unchecked_mut(tail), item) }
            rb.tail.store(next_tail, Ordering::Release);
            Ok(())
        } else {
            Err(BufferFullError)
        }
    }

    /// Adds an `item` to the end of the queue
    ///
    /// Returns `BufferFullError` if the queue is full
    #[cfg(not(target_has_atomic = "ptr"))]
    pub fn enqueue(&mut self, item: T) -> Result<(), BufferFullError> {
        let rb = unsafe { self.rb.as_mut() };

        let n = rb.capacity() + 1;
        let buffer: &mut [T] = unsafe { rb.buffer.as_mut() };

        let next_tail = (rb.tail + 1) % n;
        // NOTE(volatile) the value of `head` can change at any time in the execution context of the
        // producer so we inform this to the compiler using a volatile load
        if next_tail != unsafe { ptr::read_volatile(&rb.head) } {
            // NOTE(ptr::write) the memory slot that we are about to write to is uninitialized. We
            // use `ptr::write` to avoid running `T`'s destructor on the uninitialized memory
            unsafe { ptr::write(buffer.get_unchecked_mut(rb.tail), item) }
            rb.tail = next_tail;
            Ok(())
        } else {
            Err(BufferFullError)
        }
    }
}

unsafe impl<T, A> Send for Producer<T, A>
where
    A: Unsize<[T]>,
    T: Send,
{
}

#[cfg(test)]
mod tests {
    use RingBuffer;

    #[test]
    fn sanity() {
        static mut RB: RingBuffer<i32, [i32; 2]> = RingBuffer::new();

        let (mut p, mut c) = unsafe { RB.split() };

        assert_eq!(c.dequeue(), None);

        p.enqueue(0).unwrap();

        assert_eq!(c.dequeue(), Some(0));
    }
}

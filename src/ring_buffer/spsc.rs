use core::ptr::{self, Shared};
use core::marker::Unsize;

use BufferFullError;
use ring_buffer::RingBuffer;

impl<T, A> RingBuffer<T, A>
where
    A: Unsize<[T]>,
{
    /// Splits a statically allocated ring buffer into producer and consumer end points
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
    pub fn dequeue(&mut self) -> Option<T> {
        let rb = unsafe { self.rb.as_ref() };

        let n = rb.capacity() + 1;
        let buffer: &[T] = unsafe { rb.buffer.as_ref() };

        let tail = rb.tail.load_relaxed();
        let head = rb.head.load_relaxed();
        if head != tail {
            let item = unsafe { ptr::read(buffer.get_unchecked(head)) };
            rb.head.store_release((head + 1) % n);
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
    pub fn enqueue(&mut self, item: T) -> Result<(), BufferFullError> {
        let rb = unsafe { self.rb.as_mut() };

        let n = rb.capacity() + 1;
        let buffer: &mut [T] = unsafe { rb.buffer.as_mut() };

        let head = rb.head.load_relaxed();
        let tail = rb.tail.load_relaxed();
        let next_tail = (tail + 1) % n;
        if next_tail != head {
            // NOTE(ptr::write) the memory slot that we are about to write to is uninitialized. We
            // use `ptr::write` to avoid running `T`'s destructor on the uninitialized memory
            unsafe { ptr::write(buffer.get_unchecked_mut(tail), item) }
            rb.tail.store_release(next_tail);
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

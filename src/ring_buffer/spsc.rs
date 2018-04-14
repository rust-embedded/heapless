use core::marker::{PhantomData, Unsize};
use core::ptr::{self, NonNull};

use BufferFullError;
use ring_buffer::RingBuffer;

impl<T, A> RingBuffer<T, A>
where
    A: Unsize<[T]>,
{
    /// Splits a statically allocated ring buffer into producer and consumer end points
    pub fn split(&mut self) -> (Producer<T, A>, Consumer<T, A>) {
        (
            Producer {
                rb: unsafe { NonNull::new_unchecked(self) },
                _marker: PhantomData,
            },
            Consumer {
                rb: unsafe { NonNull::new_unchecked(self) },
                _marker: PhantomData,
            },
        )
    }
}

/// A ring buffer "consumer"; it can dequeue items from the ring buffer
// NOTE the consumer semantically owns the `head` pointer of the ring buffer
pub struct Consumer<'a, T, A>
where
    A: Unsize<[T]>,
{
    // XXX do we need to use `NonNull` (for soundness) here?
    rb: NonNull<RingBuffer<T, A>>,
    _marker: PhantomData<&'a ()>,
}

impl<'a, T, A> Consumer<'a, T, A>
where
    A: Unsize<[T]>,
{
    /// Returns the item in the front of the queue, or `None` if the queue is empty
    pub fn dequeue(&mut self) -> Option<T> {
        let rb = unsafe { self.rb.as_ref() };

        let n = rb.capacity() + 1;
        let buffer: &[T] = unsafe { rb.buffer.as_ref() };

        let tail = rb.tail.load_acquire();
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

unsafe impl<'a, T, A> Send for Consumer<'a, T, A>
where
    A: Unsize<[T]>,
    T: Send,
{
}

/// A ring buffer "producer"; it can enqueue items into the ring buffer
// NOTE the producer semantically owns the `tail` pointer of the ring buffer
pub struct Producer<'a, T, A>
where
    A: Unsize<[T]>,
{
    // XXX do we need to use `NonNull` (for soundness) here?
    rb: NonNull<RingBuffer<T, A>>,
    _marker: PhantomData<&'a ()>,
}

impl<'a, T, A> Producer<'a, T, A>
where
    A: Unsize<[T]>,
{
    /// Adds an `item` to the end of the queue
    ///
    /// Returns a `BufferFullError` containing `item` if the queue is full
    pub fn enqueue(&mut self, item: T) -> Result<(), BufferFullError<T>> {
        let rb = unsafe { self.rb.as_mut() };

        let n = rb.capacity() + 1;
        let buffer: &mut [T] = unsafe { rb.buffer.as_mut() };

        let tail = rb.tail.load_relaxed();
        // NOTE we could replace this `load_acquire` with a `load_relaxed` and this method would be
        // sound on most architectures but that change would result in UB according to the C++
        // memory model, which is what Rust currently uses, so we err on the side of caution and
        // stick to `load_acquire`. Check issue google#sanitizers#882 for more details.
        let head = rb.head.load_acquire();
        let next_tail = (tail + 1) % n;
        if next_tail != head {
            // NOTE(ptr::write) the memory slot that we are about to write to is uninitialized. We
            // use `ptr::write` to avoid running `T`'s destructor on the uninitialized memory
            unsafe { ptr::write(buffer.get_unchecked_mut(tail), item) }
            rb.tail.store_release(next_tail);
            Ok(())
        } else {
            Err(BufferFullError(item))
        }
    }
}

unsafe impl<'a, T, A> Send for Producer<'a, T, A>
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

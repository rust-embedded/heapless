use core::marker::{PhantomData, Unsize};
use core::ptr::{self, NonNull};

use ring_buffer::{RingBuffer, Uxx};
use BufferFullError;

impl<T, A, U> RingBuffer<T, A, U>
where
    A: Unsize<[T]>,
    U: Uxx,
{
    /// Splits a statically allocated ring buffer into producer and consumer end points
    pub fn split<'rb>(&'rb mut self) -> (Producer<'rb, T, A, U>, Consumer<'rb, T, A, U>) {
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
pub struct Consumer<'a, T, A, U = usize>
where
    A: Unsize<[T]>,
    U: Uxx,
{
    // XXX do we need to use `NonNull` (for soundness) here?
    rb: NonNull<RingBuffer<T, A, U>>,
    _marker: PhantomData<&'a ()>,
}

unsafe impl<'a, T, A, U> Send for Consumer<'a, T, A, U>
where
    A: Unsize<[T]>,
    T: Send,
    U: Uxx,
{
}

/// A ring buffer "producer"; it can enqueue items into the ring buffer
// NOTE the producer semantically owns the `tail` pointer of the ring buffer
pub struct Producer<'a, T, A, U = usize>
where
    A: Unsize<[T]>,
    U: Uxx,
{
    // XXX do we need to use `NonNull` (for soundness) here?
    rb: NonNull<RingBuffer<T, A, U>>,
    _marker: PhantomData<&'a ()>,
}

unsafe impl<'a, T, A, U> Send for Producer<'a, T, A, U>
where
    A: Unsize<[T]>,
    T: Send,
    U: Uxx,
{
}

macro_rules! impl_ {
    ($uxx:ident) => {
        impl<'a, T, A> Consumer<'a, T, A, $uxx>
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
                    let item = unsafe { ptr::read(buffer.get_unchecked(usize::from(head))) };
                    rb.head.store_release((head + 1) % n);
                    Some(item)
                } else {
                    None
                }
            }
        }

        impl<'a, T, A> Producer<'a, T, A, $uxx>
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

                let tail = rb.tail.load_relaxed();
                // NOTE we could replace this `load_acquire` with a `load_relaxed` and this method
                // would be sound on most architectures but that change would result in UB according
                // to the C++ memory model, which is what Rust currently uses, so we err on the side
                // of caution and stick to `load_acquire`. Check issue google#sanitizers#882 for
                // more details.
                let head = rb.head.load_acquire();
                let next_tail = (tail + 1) % n;
                if next_tail != head {
                    // NOTE(ptr::write) the memory slot that we are about to write to is
                    // uninitialized. We use `ptr::write` to avoid running `T`'s destructor on the
                    // uninitialized memory
                    unsafe { ptr::write(buffer.get_unchecked_mut(usize::from(tail)), item) }
                    rb.tail.store_release(next_tail);
                    Ok(())
                } else {
                    Err(BufferFullError)
                }
            }
        }
    };
}

impl_!(u8);
impl_!(u16);
impl_!(usize);

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

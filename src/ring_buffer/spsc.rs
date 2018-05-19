use core::marker::PhantomData;
use core::ops::Add;
use core::ptr::{self, NonNull};

use generic_array::typenum::{Sum, U1, Unsigned};
use generic_array::ArrayLength;

use ring_buffer::{RingBuffer, Uxx};

impl<T, N, U> RingBuffer<T, N, U>
where
    N: Add<U1> + Unsigned,
    Sum<N, U1>: ArrayLength<T>,
    U: Uxx,
{
    /// Splits a statically allocated ring buffer into producer and consumer end points
    pub fn split<'rb>(&'rb mut self) -> (Producer<'rb, T, N, U>, Consumer<'rb, T, N, U>) {
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
pub struct Consumer<'a, T, N, U = usize>
where
    N: Add<U1> + Unsigned,
    Sum<N, U1>: ArrayLength<T>,
    U: Uxx,
{
    // XXX do we need to use `NonNull` (for soundness) here?
    rb: NonNull<RingBuffer<T, N, U>>,
    _marker: PhantomData<&'a ()>,
}

unsafe impl<'a, T, N, U> Send for Consumer<'a, T, N, U>
where
    N: Add<U1> + Unsigned,
    Sum<N, U1>: ArrayLength<T>,
    T: Send,
    U: Uxx,
{
}

/// A ring buffer "producer"; it can enqueue items into the ring buffer
// NOTE the producer semantically owns the `tail` pointer of the ring buffer
pub struct Producer<'a, T, N, U = usize>
where
    N: Add<U1> + Unsigned,
    Sum<N, U1>: ArrayLength<T>,
    U: Uxx,
{
    // XXX do we need to use `NonNull` (for soundness) here?
    rb: NonNull<RingBuffer<T, N, U>>,
    _marker: PhantomData<&'a ()>,
}

unsafe impl<'a, T, N, U> Send for Producer<'a, T, N, U>
where
    N: Add<U1> + Unsigned,
    Sum<N, U1>: ArrayLength<T>,
    T: Send,
    U: Uxx,
{
}

macro_rules! impl_ {
    ($uxx:ident) => {
        impl<'a, T, N> Consumer<'a, T, N, $uxx>
        where
            N: Add<U1> + Unsigned,
            Sum<N, U1>: ArrayLength<T>,
        {
            /// Returns the item in the front of the queue, or `None` if the queue is empty
            pub fn dequeue(&mut self) -> Option<T> {
                let tail = unsafe { self.rb.as_ref().tail.load_acquire() };
                let head = unsafe { self.rb.as_ref().head.load_relaxed() };

                if head != tail {
                    Some(unsafe { self._dequeue(head) })
                } else {
                    None
                }
            }

            /// Returns the item in the front of the queue, without checking if it's empty
            ///
            /// # Unsafety
            ///
            /// If the queue is empty this is equivalent to calling `mem::uninitialized`
            pub unsafe fn dequeue_unchecked(&mut self) -> T {
                let head = self.rb.as_ref().head.load_relaxed();
                debug_assert_ne!(head, self.rb.as_ref().tail.load_acquire());
                self._dequeue(head)
            }

            unsafe fn _dequeue(&mut self, head: $uxx) -> T {
                let rb = self.rb.as_ref();

                let n = rb.capacity() + 1;
                let buffer: &[T] = rb.buffer.as_ref();

                let item = ptr::read(buffer.get_unchecked(usize::from(head)));
                rb.head.store_release((head + 1) % n);
                item
            }
        }

        impl<'a, T, N> Producer<'a, T, N, $uxx>
        where
            N: Add<U1> + Unsigned,
            Sum<N, U1>: ArrayLength<T>,
        {
            /// Adds an `item` to the end of the queue
            ///
            /// Returns back the `item` if the queue is full
            pub fn enqueue(&mut self, item: T) -> Result<(), T> {
                let n = unsafe { self.rb.as_ref().capacity() + 1 };
                let tail = unsafe { self.rb.as_ref().tail.load_relaxed() };
                // NOTE we could replace this `load_acquire` with a `load_relaxed` and this method
                // would be sound on most architectures but that change would result in UB according
                // to the C++ memory model, which is what Rust currently uses, so we err on the side
                // of caution and stick to `load_acquire`. Check issue google#sanitizers#882 for
                // more details.
                let head = unsafe { self.rb.as_ref().head.load_acquire() };
                let next_tail = (tail + 1) % n;
                if next_tail != head {
                    unsafe { self._enqueue(tail, item) };
                    Ok(())
                } else {
                    Err(item)
                }
            }

            /// Adds an `item` to the end of the queue without checking if it's full
            ///
            /// **WARNING** If the queue is full this operation will make the queue appear empty to
            /// the `Consumer`, thus *leaking* (destructors won't run) all the elements that were in
            /// the queue.
            pub fn enqueue_unchecked(&mut self, item: T) {
                unsafe {
                    let tail = self.rb.as_ref().tail.load_relaxed();
                    debug_assert_ne!(
                        (tail + 1) % (self.rb.as_ref().capacity() + 1),
                        self.rb.as_ref().head.load_acquire()
                    );
                    self._enqueue(tail, item);
                }
            }

            unsafe fn _enqueue(&mut self, tail: $uxx, item: T) {
                let rb = self.rb.as_mut();

                let n = rb.capacity() + 1;
                let buffer: &mut [T] = rb.buffer.as_mut();

                let next_tail = (tail + 1) % n;
                // NOTE(ptr::write) the memory slot that we are about to write to is
                // uninitialized. We use `ptr::write` to avoid running `T`'s destructor on the
                // uninitialized memory
                ptr::write(buffer.get_unchecked_mut(usize::from(tail)), item);
                rb.tail.store_release(next_tail);
            }
        }
    };
}

impl_!(u8);
impl_!(u16);
impl_!(usize);

#[cfg(test)]
mod tests {
    use consts::*;
    use RingBuffer;

    #[test]
    fn sanity() {
        let mut rb: RingBuffer<i32, U2> = RingBuffer::new();

        let (mut p, mut c) = rb.split();

        assert_eq!(c.dequeue(), None);

        p.enqueue(0).unwrap();

        assert_eq!(c.dequeue(), Some(0));
    }
}

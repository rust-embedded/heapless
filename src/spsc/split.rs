use core::{marker::PhantomData, ptr::NonNull};

use generic_array::ArrayLength;

use crate::{
    sealed::spsc as sealed,
    spsc::{MultiCore, Queue},
};

impl<T, N, U, C> Queue<T, N, U, C>
where
    N: ArrayLength<T>,
    U: sealed::Uxx,
    C: sealed::XCore,
{
    /// Splits a statically allocated queue into producer and consumer end points
    pub fn split<'rb>(&'rb mut self) -> (Producer<'rb, T, N, U, C>, Consumer<'rb, T, N, U, C>) {
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

/// A queue "consumer"; it can dequeue items from the queue
// NOTE the consumer semantically owns the `head` pointer of the queue
pub struct Consumer<'a, T, N, U = usize, C = MultiCore>
where
    N: ArrayLength<T>,
    U: sealed::Uxx,
    C: sealed::XCore,
{
    rb: NonNull<Queue<T, N, U, C>>,
    _marker: PhantomData<&'a ()>,
}

unsafe impl<'a, T, N, U, C> Send for Consumer<'a, T, N, U, C>
where
    N: ArrayLength<T>,
    T: Send,
    U: sealed::Uxx,
    C: sealed::XCore,
{
}

/// A queue "producer"; it can enqueue items into the queue
// NOTE the producer semantically owns the `tail` pointer of the queue
pub struct Producer<'a, T, N, U = usize, C = MultiCore>
where
    N: ArrayLength<T>,
    U: sealed::Uxx,
    C: sealed::XCore,
{
    rb: NonNull<Queue<T, N, U, C>>,
    _marker: PhantomData<&'a ()>,
}

unsafe impl<'a, T, N, U> Send for Producer<'a, T, N, U>
where
    N: ArrayLength<T>,
    T: Send,
    U: sealed::Uxx,
{
}

macro_rules! impl_ {
    ($uxx:ident) => {
        impl<'a, T, N, C> Consumer<'a, T, N, $uxx, C>
        where
            N: ArrayLength<T>,
            C: sealed::XCore,
        {
            /// Returns if there are any items to dequeue. When this returns true, at least the
            /// first subsequent dequeue will succeed.
            pub fn ready(&self) -> bool {
                let head = unsafe { self.rb.as_ref().0.head.load_relaxed() };
                let tail = unsafe { self.rb.as_ref().0.tail.load_acquire() }; // ▼
                return head != tail;
            }

            /// Returns the item in the front of the queue, or `None` if the queue is empty
            pub fn dequeue(&mut self) -> Option<T> {
                let head = unsafe { self.rb.as_ref().0.head.load_relaxed() };
                let tail = unsafe { self.rb.as_ref().0.tail.load_acquire() }; // ▼

                if head != tail {
                    Some(unsafe { self._dequeue(head) }) // ▲
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
                let head = self.rb.as_ref().0.head.load_relaxed();
                debug_assert_ne!(head, self.rb.as_ref().0.tail.load_acquire());
                self._dequeue(head) // ▲
            }

            unsafe fn _dequeue(&mut self, head: $uxx) -> T {
                let rb = self.rb.as_ref();

                let cap = rb.capacity();

                let item = (rb.0.buffer.as_ptr() as *const T)
                    .add(usize::from(head % cap))
                    .read();
                rb.0.head.store_release(head.wrapping_add(1)); // ▲
                item
            }
        }

        impl<'a, T, N, C> Producer<'a, T, N, $uxx, C>
        where
            N: ArrayLength<T>,
            C: sealed::XCore,
        {
            /// Returns if there is any space to enqueue a new item. When this returns true, at
            /// least the first subsequent enqueue will succeed.
            pub fn ready(&self) -> bool {
                let cap = unsafe { self.rb.as_ref().capacity() };

                let tail = unsafe { self.rb.as_ref().0.tail.load_relaxed() };
                // NOTE we could replace this `load_acquire` with a `load_relaxed` and this method
                // would be sound on most architectures but that change would result in UB according
                // to the C++ memory model, which is what Rust currently uses, so we err on the side
                // of caution and stick to `load_acquire`. Check issue google#sanitizers#882 for
                // more details.
                let head = unsafe { self.rb.as_ref().0.head.load_acquire() };
                return head.wrapping_add(cap) != tail;
            }

            /// Adds an `item` to the end of the queue
            ///
            /// Returns back the `item` if the queue is full
            pub fn enqueue(&mut self, item: T) -> Result<(), T> {
                let cap = unsafe { self.rb.as_ref().capacity() };
                let tail = unsafe { self.rb.as_ref().0.tail.load_relaxed() };
                // NOTE we could replace this `load_acquire` with a `load_relaxed` and this method
                // would be sound on most architectures but that change would result in UB according
                // to the C++ memory model, which is what Rust currently uses, so we err on the side
                // of caution and stick to `load_acquire`. Check issue google#sanitizers#882 for
                // more details.
                let head = unsafe { self.rb.as_ref().0.head.load_acquire() }; // ▼

                if tail.wrapping_sub(head) > cap - 1 {
                    Err(item)
                } else {
                    unsafe { self._enqueue(tail, item) }; // ▲
                    Ok(())
                }
            }

            /// Adds an `item` to the end of the queue without checking if it's full
            ///
            /// # Unsafety
            ///
            /// If the queue is full this operation will leak a value (T's destructor won't run on
            /// the value that got overwritten by `item`), *and* will allow the `dequeue` operation
            /// to create a copy of `item`, which could result in `T`'s destructor running on `item`
            /// twice.
            pub unsafe fn enqueue_unchecked(&mut self, item: T) {
                let tail = self.rb.as_ref().0.tail.load_relaxed();
                debug_assert_ne!(tail.wrapping_add(1), self.rb.as_ref().0.head.load_acquire());
                self._enqueue(tail, item); // ▲
            }

            unsafe fn _enqueue(&mut self, tail: $uxx, item: T) {
                let rb = self.rb.as_mut();

                let cap = rb.capacity();

                // NOTE(ptr::write) the memory slot that we are about to write to is
                // uninitialized. We use `ptr::write` to avoid running `T`'s destructor on the
                // uninitialized memory
                (rb.0.buffer.as_mut_ptr() as *mut T)
                    .add(usize::from(tail % cap))
                    .write(item);
                rb.0.tail.store_release(tail.wrapping_add(1)); // ▲
            }
        }
    };
}

impl_!(u8);
impl_!(u16);
impl_!(usize);

#[cfg(test)]
mod tests {
    use crate::{consts::*, spsc::Queue};

    #[test]
    fn sanity() {
        let mut rb: Queue<i32, U2> = Queue::new();

        let (mut p, mut c) = rb.split();

        assert_eq!(c.dequeue(), None);

        p.enqueue(0).unwrap();

        assert_eq!(c.dequeue(), Some(0));
    }
}

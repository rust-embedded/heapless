use core::ptr::{self, Shared};
use core::marker::Unsize;

use Error;
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
    pub fn dequeue(&mut self) -> Option<T> {
        let rb = unsafe { self.rb.as_mut() };
        let n = rb.capacity() + 1;
        let buffer: &[T] = unsafe { rb.buffer.as_ref() };

        // NOTE(volatile) the value of `tail` can change at any time in the context of the consumer
        // so we inform this to the compiler using a volatile load
        if rb.head != unsafe { ptr::read_volatile(&rb.tail) } {
            let item = unsafe { ptr::read(&buffer[rb.head]) };
            rb.head = (rb.head + 1) % n;
            Some(item)
        } else {
            None
        }
    }
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
    pub fn enqueue(&mut self, item: T) -> Result<(), Error> {
        let rb = unsafe { self.rb.as_mut() };
        let n = rb.capacity() + 1;
        let buffer: &mut [T] = unsafe { rb.buffer.as_mut() };

        let next_tail = (rb.tail + 1) % n;
        // NOTE(volatile) the value of `head` can change at any time in the context of the producer
        // so we inform this to the compiler using a volatile load
        if next_tail != unsafe { ptr::read_volatile(&rb.head) } {
            // NOTE(ptr::write) the memory slot that we are about to write to is uninitialized. We
            // use `ptr::write` to avoid running `T`'s destructor on the uninitialized memory
            unsafe { ptr::write(&mut buffer[rb.tail], item) }
            rb.tail = next_tail;
            Ok(())
        } else {
            Err(Error::Full)
        }
    }
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

use core::marker::{PhantomData, Unsize};
use core::ptr;

use untagged_option::UntaggedOption;

use Error;

pub use self::spsc::{Consumer, Producer};

mod spsc;

/// An statically allocated ring buffer backed by an array with type `A`
pub struct RingBuffer<T, A>
where
    // FIXME(rust-lang/rust#44580) use "const generics" instead of `Unsize`
    A: Unsize<[T]>,
{
    _marker: PhantomData<[T]>,
    buffer: UntaggedOption<A>,
    // this is from where we dequeue items
    head: usize,
    // this is where we enqueue new items
    tail: usize,
}

impl<T, A> RingBuffer<T, A>
where
    A: Unsize<[T]>,
{
    /// Creates an empty ring buffer with capacity equals to the length of the array `A` *minus
    /// one*.
    pub const fn new() -> Self {
        RingBuffer {
            _marker: PhantomData,
            buffer: UntaggedOption::none(),
            head: 0,
            tail: 0,
        }
    }

    pub fn capacity(&self) -> usize {
        let buffer: &[T] = unsafe { self.buffer.as_ref() };
        buffer.len() - 1
    }

    pub fn dequeue(&mut self) -> Option<T> {
        let n = self.capacity() + 1;
        let buffer: &[T] = unsafe { self.buffer.as_ref() };

        if self.head != self.tail {
            let item = unsafe { ptr::read(buffer.as_ptr().offset(self.head as isize)) };
            self.head = (self.head + 1) % n;
            Some(item)
        } else {
            None
        }
    }

    pub fn enqueue(&mut self, item: T) -> Result<(), Error> {
        let n = self.capacity() + 1;
        let buffer: &mut [T] = unsafe { self.buffer.as_mut() };

        let next_tail = (self.tail + 1) % n;
        if next_tail != self.head {
            // NOTE(ptr::write) the memory slot that we are about to write to is uninitialized. We
            // use `ptr::write` to avoid running `T`'s destructor on the uninitialized memory
            unsafe { ptr::write(buffer.as_mut_ptr().offset(self.tail as isize), item) }
            self.tail = next_tail;
            Ok(())
        } else {
            Err(Error::Full)
        }
    }

    pub fn len(&self) -> usize {
        if self.head > self.tail {
            self.head - self.tail
        } else {
            self.tail - self.head
        }
    }

    /// Iterates from the front of the queue to the back
    pub fn iter(&self) -> Iter<T, A> {
        Iter {
            rb: self,
            index: 0,
            len: self.len(),
        }
    }

    /// Mutable version of `iter`
    pub fn iter_mut(&mut self) -> IterMut<T, A> {
        let len = self.len();
        IterMut {
            rb: self,
            index: 0,
            len,
        }
    }
}

impl<T, A> Drop for RingBuffer<T, A>
where
    A: Unsize<[T]>,
{
    fn drop(&mut self) {
        for item in self {
            unsafe {
                ptr::drop_in_place(item);
            }
        }
    }
}

impl<'a, T, A> IntoIterator for &'a RingBuffer<T, A>
where
    A: Unsize<[T]>,
{
    type Item = &'a T;
    type IntoIter = Iter<'a, T, A>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T, A> IntoIterator for &'a mut RingBuffer<T, A>
where
    A: Unsize<[T]>,
{
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T, A>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

pub struct Iter<'a, T, A>
where
    A: Unsize<[T]> + 'a,
    T: 'a,
{
    rb: &'a RingBuffer<T, A>,
    index: usize,
    len: usize,
}

pub struct IterMut<'a, T, A>
where
    A: Unsize<[T]> + 'a,
    T: 'a,
{
    rb: &'a mut RingBuffer<T, A>,
    index: usize,
    len: usize,
}

impl<'a, T, A> Iterator for Iter<'a, T, A>
where
    A: Unsize<[T]> + 'a,
    T: 'a,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        if self.index < self.len {
            let buffer: &[T] = unsafe { self.rb.buffer.as_ref() };
            let ptr = buffer.as_ptr();
            let i = (self.rb.head + self.index) % (self.rb.capacity() + 1);
            self.index += 1;
            Some(unsafe { &*ptr.offset(i as isize) })
        } else {
            None
        }
    }
}

impl<'a, T, A> Iterator for IterMut<'a, T, A>
where
    A: Unsize<[T]> + 'a,
    T: 'a,
{
    type Item = &'a mut T;

    fn next(&mut self) -> Option<&'a mut T> {
        if self.index < self.len {
            let capacity = self.rb.capacity() + 1;
            let buffer: &mut [T] = unsafe { self.rb.buffer.as_mut() };
            let ptr: *mut T = buffer.as_mut_ptr();
            let i = (self.rb.head + self.index) % capacity;
            self.index += 1;
            Some(unsafe { &mut *ptr.offset(i as isize) })
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use RingBuffer;

    #[test]
    fn drop() {
        struct Droppable;
        impl Droppable {
            fn new() -> Self {
                unsafe {
                    COUNT += 1;
                }
                Droppable
            }
        }
        impl Drop for Droppable {
            fn drop(&mut self) {
                unsafe {
                    COUNT -= 1;
                }
            }
        }

        static mut COUNT: i32 = 0;


        {
            let mut v: RingBuffer<Droppable, [Droppable; 4]> = RingBuffer::new();
            v.enqueue(Droppable::new()).unwrap();
            v.enqueue(Droppable::new()).unwrap();
            v.dequeue().unwrap();
        }

        assert_eq!(unsafe { COUNT }, 0);

        {
            let mut v: RingBuffer<Droppable, [Droppable; 4]> = RingBuffer::new();
            v.enqueue(Droppable::new()).unwrap();
            v.enqueue(Droppable::new()).unwrap();
        }

        assert_eq!(unsafe { COUNT }, 0);
    }

    #[test]
    fn full() {
        let mut rb: RingBuffer<i32, [i32; 4]> = RingBuffer::new();

        rb.enqueue(0).unwrap();
        rb.enqueue(1).unwrap();
        rb.enqueue(2).unwrap();

        assert!(rb.enqueue(3).is_err());
    }

    #[test]
    fn iter() {
        let mut rb: RingBuffer<i32, [i32; 4]> = RingBuffer::new();

        rb.enqueue(0).unwrap();
        rb.enqueue(1).unwrap();
        rb.enqueue(2).unwrap();

        let mut items = rb.iter();

        assert_eq!(items.next(), Some(&0));
        assert_eq!(items.next(), Some(&1));
        assert_eq!(items.next(), Some(&2));
        assert_eq!(items.next(), None);
    }

    #[test]
    fn iter_mut() {
        let mut rb: RingBuffer<i32, [i32; 4]> = RingBuffer::new();

        rb.enqueue(0).unwrap();
        rb.enqueue(1).unwrap();
        rb.enqueue(2).unwrap();

        let mut items = rb.iter_mut();

        assert_eq!(items.next(), Some(&mut 0));
        assert_eq!(items.next(), Some(&mut 1));
        assert_eq!(items.next(), Some(&mut 2));
        assert_eq!(items.next(), None);
    }

    #[test]
    fn sanity() {
        let mut rb: RingBuffer<i32, [i32; 4]> = RingBuffer::new();

        assert_eq!(rb.dequeue(), None);

        rb.enqueue(0).unwrap();

        assert_eq!(rb.dequeue(), Some(0));

        assert_eq!(rb.dequeue(), None);
    }

    #[test]
    fn wrap_around() {
        let mut rb: RingBuffer<i32, [i32; 4]> = RingBuffer::new();

        rb.enqueue(0).unwrap();
        rb.enqueue(1).unwrap();
        rb.enqueue(2).unwrap();
        rb.dequeue().unwrap();
        rb.dequeue().unwrap();
        rb.dequeue().unwrap();
        rb.enqueue(3).unwrap();
        rb.enqueue(4).unwrap();

        assert_eq!(rb.len(), 2);
    }
}

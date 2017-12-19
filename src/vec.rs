use core::marker::{PhantomData, Unsize};
use core::{ops, ptr, slice};

use untagged_option::UntaggedOption;

use BufferFullError;

/// A [`Vec`], *vector*, backed by a fixed size array
///
/// [`Vec`]: https://doc.rust-lang.org/std/vec/struct.Vec.html
pub struct Vec<T, A>
where
    // FIXME(rust-lang/rust#44580) use "const generics" instead of `Unsize`
    A: Unsize<[T]>,
{
    _marker: PhantomData<[T]>,
    buffer: UntaggedOption<A>,
    len: usize,
}

impl<T, A> Vec<T, A>
where
    A: Unsize<[T]>,
{
    /// Constructs a new, empty `Vec<T>` backed by the array `A`
    pub const fn new() -> Self {
        Vec {
            _marker: PhantomData,
            buffer: UntaggedOption::none(),
            len: 0,
        }
    }

    /// Returns the maximum number of elements the vector can hold
    pub fn capacity(&self) -> usize {
        let buffer: &[T] = unsafe { self.buffer.as_ref() };
        buffer.len()
    }

    /// Clears the vector, removing all values.
    pub fn clear(&mut self) {
        self.truncate(0);
    }

    /// Removes the last element from a vector and return it, or `None` if it's empty
    pub fn pop(&mut self) -> Option<T> {
        let buffer: &[T] = unsafe { self.buffer.as_ref() };

        if self.len != 0 {
            self.len -= 1;
            let item = unsafe { ptr::read(&buffer[self.len]) };
            Some(item)
        } else {
            None
        }
    }

    /// Appends an element to the back of the collection
    ///
    /// Returns `BufferFullError` if the vector is full
    pub fn push(&mut self, item: T) -> Result<(), BufferFullError> {
        let capacity = self.capacity();
        let buffer: &mut [T] = unsafe { self.buffer.as_mut() };

        if self.len < capacity {
            // NOTE(ptr::write) the memory slot that we are about to write to is uninitialized. We
            // use `ptr::write` to avoid running `T`'s destructor on the uninitialized memory
            unsafe { ptr::write(&mut buffer[self.len], item) }
            self.len += 1;
            Ok(())
        } else {
            Err(BufferFullError)
        }
    }

    /// Shortens the vector, keeping the first `len` elements and dropping the rest.
    pub fn truncate(&mut self, len: usize) {
        unsafe {
            // drop any extra elements
            while len < self.len {
                // decrement len before the drop_in_place(), so a panic on Drop
                // doesn't re-drop the just-failed value.
                self.len -= 1;
                let len = self.len;
                ptr::drop_in_place(self.get_unchecked_mut(len));
            }
        }
    }
}

impl<T, A> Drop for Vec<T, A>
where
    A: Unsize<[T]>,
{
    fn drop(&mut self) {
        unsafe { ptr::drop_in_place(&mut self[..]) }
    }
}

impl<'a, T, A> IntoIterator for &'a Vec<T, A>
where
    A: Unsize<[T]>,
{
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T, A> IntoIterator for &'a mut Vec<T, A>
where
    A: Unsize<[T]>,
{
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T, A> ops::Deref for Vec<T, A>
where
    A: Unsize<[T]>,
{
    type Target = [T];

    fn deref(&self) -> &[T] {
        let buffer: &[T] = unsafe { self.buffer.as_ref() };
        &buffer[..self.len]
    }
}

impl<T, A> ops::DerefMut for Vec<T, A>
where
    A: Unsize<[T]>,
{
    fn deref_mut(&mut self) -> &mut [T] {
        let len = self.len();
        let buffer: &mut [T] = unsafe { self.buffer.as_mut() };
        &mut buffer[..len]
    }
}

#[cfg(test)]
mod tests {
    use Vec;

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
            let mut v: Vec<Droppable, [Droppable; 2]> = Vec::new();
            v.push(Droppable::new()).unwrap();
            v.push(Droppable::new()).unwrap();
            v.pop().unwrap();
        }

        assert_eq!(unsafe { COUNT }, 0);

        {
            let mut v: Vec<Droppable, [Droppable; 2]> = Vec::new();
            v.push(Droppable::new()).unwrap();
            v.push(Droppable::new()).unwrap();
        }

        assert_eq!(unsafe { COUNT }, 0);
    }

    #[test]
    fn full() {
        let mut v: Vec<i32, [i32; 4]> = Vec::new();

        v.push(0).unwrap();
        v.push(1).unwrap();
        v.push(2).unwrap();
        v.push(3).unwrap();

        assert!(v.push(4).is_err());
    }

    #[test]
    fn iter() {
        let mut v: Vec<i32, [i32; 4]> = Vec::new();

        v.push(0).unwrap();
        v.push(1).unwrap();
        v.push(2).unwrap();
        v.push(3).unwrap();

        let mut items = v.iter();

        assert_eq!(items.next(), Some(&0));
        assert_eq!(items.next(), Some(&1));
        assert_eq!(items.next(), Some(&2));
        assert_eq!(items.next(), Some(&3));
        assert_eq!(items.next(), None);
    }

    #[test]
    fn iter_mut() {
        let mut v: Vec<i32, [i32; 4]> = Vec::new();

        v.push(0).unwrap();
        v.push(1).unwrap();
        v.push(2).unwrap();
        v.push(3).unwrap();

        let mut items = v.iter_mut();

        assert_eq!(items.next(), Some(&mut 0));
        assert_eq!(items.next(), Some(&mut 1));
        assert_eq!(items.next(), Some(&mut 2));
        assert_eq!(items.next(), Some(&mut 3));
        assert_eq!(items.next(), None);
    }

    #[test]
    fn push_and_pop() {
        let mut v: Vec<i32, [i32; 4]> = Vec::new();
        assert_eq!(v.len(), 0);

        assert_eq!(v.pop(), None);
        assert_eq!(v.len(), 0);

        v.push(0).unwrap();
        assert_eq!(v.len(), 1);

        assert_eq!(v.pop(), Some(0));
        assert_eq!(v.len(), 0);

        assert_eq!(v.pop(), None);
        assert_eq!(v.len(), 0);
    }
}

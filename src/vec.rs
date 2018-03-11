use core::marker::{PhantomData, Unsize};
use core::{fmt, ops, ptr, slice};

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

    /// Clones and appends all elements in a slice to the `Vec`.
    ///
    /// Iterates over the slice `other`, clones each element, and then appends
    /// it to this `Vec`. The `other` vector is traversed in-order.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::Vec;
    ///
    /// let mut vec = Vec::<u8, [u8; 8]>::new();
    /// vec.push(1).unwrap();
    /// vec.extend_from_slice(&[2, 3, 4]).unwrap();
    /// assert_eq!(*vec, [1, 2, 3, 4]);
    /// ```
    pub fn extend_from_slice(&mut self, other: &[T]) -> Result<(), BufferFullError>
    where
        T: Clone,
    {
        if self.len() + other.len() > self.capacity() {
            // won't fit in the `Vec`; don't modify anything and return an error
            Err(BufferFullError)
        } else {
            for elem in other {
                self.push(elem.clone())?
            }
            Ok(())
        }
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

    /// Resizes the Vec in-place so that len is equal to new_len.
    ///
    /// If new_len is greater than len, the Vec is extended by the
    /// difference, with each additional slot filled with value. If
    /// new_len is less than len, the Vec is simply truncated.
    ///
    /// See also [`resize_default`].
    pub fn resize(&mut self, new_len: usize, value: T) -> Result<(), BufferFullError>
    where
        T: Clone,
    {
        if new_len > self.capacity() {
            return Err(BufferFullError);
        }

        if new_len > self.len {
            while self.len < new_len {
                self.push(value.clone())?;
            }
        } else {
            self.truncate(new_len);
        }

        Ok(())
    }

    /// Resizes the `Vec` in-place so that `len` is equal to `new_len`.
    ///
    /// If `new_len` is greater than `len`, the `Vec` is extended by the
    /// difference, with each additional slot filled with `Default::default()`.
    /// If `new_len` is less than `len`, the `Vec` is simply truncated.
    ///
    /// See also [`resize`].
    pub fn resize_default(&mut self, new_len: usize) -> Result<(), BufferFullError>
    where
        T: Clone + Default,
    {
        self.resize(new_len, T::default())
    }

    /// Removes an element from the vector and returns it.
    ///
    /// The removed element is replaced by the last element of the vector.
    ///
    /// This does not preserve ordering, but is O(1).
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::Vec;
    ///
    /// let mut v: Vec<_, [_; 8]> = Vec::new();
    /// v.push("foo").unwrap();
    /// v.push("bar").unwrap();
    /// v.push("baz").unwrap();
    /// v.push("qux").unwrap();
    ///
    /// assert_eq!(v.swap_remove(1), "bar");
    /// assert_eq!(&*v, ["foo", "qux", "baz"]);
    ///
    /// assert_eq!(v.swap_remove(0), "foo");
    /// assert_eq!(&*v, ["baz", "qux"]);
    /// ```
    pub fn swap_remove(&mut self, index: usize) -> T {
        let length = self.len();
        self.swap(index, length - 1);
        self.pop().unwrap()
    }
}

impl<T, A> fmt::Debug for Vec<T, A>
where
    A: Unsize<[T]>,
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let slice: &[T] = &**self;
        slice.fmt(f)
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

impl<T, A, B> PartialEq<Vec<T, B>> for Vec<T, A>
where
    A: Unsize<[T]>,
    B: Unsize<[T]>,
    T: PartialEq,
{
    fn eq(&self, rhs: &Vec<T, B>) -> bool {
        PartialEq::eq(&**self, &**rhs)
    }
}

impl<T, A> Eq for Vec<T, A>
where
    A: Unsize<[T]>,
    T: Eq,
{
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

impl<T, A> AsRef<Vec<T, A>> for Vec<T, A>
where
    A: Unsize<[T]>,
{
    #[inline]
    fn as_ref(&self) -> &Vec<T, A> {
        self
    }
}

impl<T, A> AsMut<Vec<T, A>> for Vec<T, A>
where
    A: Unsize<[T]>,
{
    #[inline]
    fn as_mut(&mut self) -> &mut Vec<T, A> {
        self
    }
}

impl<T, A> AsRef<[T]> for Vec<T, A>
where
    A: Unsize<[T]>,
{
    #[inline]
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T, A> AsMut<[T]> for Vec<T, A>
where
    A: Unsize<[T]>,
{
    #[inline]
    fn as_mut(&mut self) -> &mut [T] {
        self
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
    fn eq() {
        let mut xs: Vec<i32, [i32; 4]> = Vec::new();
        let mut ys: Vec<i32, [i32; 8]> = Vec::new();

        assert_eq!(xs, ys);

        xs.push(1).unwrap();
        ys.push(1).unwrap();

        assert_eq!(xs, ys);
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

    #[test]
    fn resize_size_limit() {
        let mut v: Vec<u8, [u8; 4]> = Vec::new();

        v.resize(0, 0).unwrap();
        v.resize(4, 0).unwrap();
        v.resize(5, 0).err().expect("BufferFullError");
    }

    #[test]
    fn resize_length_cases() {
        let mut v: Vec<u8, [u8; 4]> = Vec::new();

        assert_eq!(v.len(), 0);

        // Grow by 1
        v.resize(1, 0).unwrap();
        assert_eq!(v.len(), 1);

        // Grow by 2
        v.resize(3, 0).unwrap();
        assert_eq!(v.len(), 3);

        // Resize to current size
        v.resize(3, 0).unwrap();
        assert_eq!(v.len(), 3);

        // Shrink by 1
        v.resize(2, 0).unwrap();
        assert_eq!(v.len(), 2);

        // Shrink by 2
        v.resize(0, 0).unwrap();
        assert_eq!(v.len(), 0);
    }

    #[test]
    fn resize_contents() {
        let mut v: Vec<u8, [u8; 4]> = Vec::new();

        // New entries take supplied value when growing
        v.resize(1, 17).unwrap();
        assert_eq!(v[0], 17);

        // Old values aren't changed when growing
        v.resize(2, 18).unwrap();
        assert_eq!(v[0], 17);
        assert_eq!(v[1], 18);

        // Old values aren't changed when length unchanged
        v.resize(2, 0).unwrap();
        assert_eq!(v[0], 17);
        assert_eq!(v[1], 18);

        // Old values aren't changed when shrinking
        v.resize(1, 0).unwrap();
        assert_eq!(v[0], 17);
    }

    #[test]
    fn resize_default() {
        let mut v: Vec<u8, [u8; 4]> = Vec::new();

        // resize_default is implemented using resize, so just check the
        // correct value is being written.
        v.resize_default(1).unwrap();
        assert_eq!(v[0], 0);
    }
}

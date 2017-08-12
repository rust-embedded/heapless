
#![deny(missing_docs)]
#![deny(warnings)]

use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};
use core::ptr;
use core::cmp;

/// A continuous, growable array type
pub struct Vec<T, A>
where
    A: AsMut<[T]> + AsRef<[T]>,
    T: Copy,
{
    _marker: PhantomData<[T]>,
    array: A,
    len: usize,
}

impl<T, A> Vec<T, A>
where
    A: AsMut<[T]> + AsRef<[T]>,
    T: Copy,
{
    /// Creates a new vector using `array` as the backup storage
    ///
    /// # Example
    /// ```
    /// #![feature(const_fn)]
    /// use heapless::Vec;
    /// const LEN: usize = 16;
    /// // with let
    /// let vec_let = Vec::new([0;LEN]);
    /// // with const
    /// const VEC_CONST: Vec<u8, [u8; LEN]> = Vec::new([0;LEN]);
    /// // with static
    /// static VEC: Vec<u8, [u8; LEN]> = Vec::new([0;LEN]);
    /// // with slice
    /// let mut array = [0_usize; 8];
    /// let mut vec_slice = Vec::new(&mut array);
    /// ```
    pub const fn new(array: A) -> Self {
        Vec {
            _marker: PhantomData,
            array: array,
            len: 0,
        }
    }

    /// Creates a new vector using `array` as the backup storage.
    /// Keeps the values and length of the array.
    /// The backup storage is completly used upon creation.
    ///
    /// # Example
    /// ```
    /// use heapless::Vec;
    /// let vec = Vec::from_array([1,2,3]);
    /// assert!(vec.is_full());
    /// ```
    pub fn from_array(array: A) -> Self {
        let len = array.as_ref().len();
        Vec {
            _marker: PhantomData,
            array: array,
            len: len,
        }
    }

    /// Returns the capacity of this vector
    ///
    /// # Example
    /// ```
    /// use heapless::Vec;
    /// const LEN: usize = 16;
    /// let vec = Vec::new([0;LEN]);
    /// assert_eq!(vec.capacity(), LEN);
    /// ```
    pub fn capacity(&self) -> usize {
        self.array.as_ref().len()
    }

    /// Returns the current length of this vector
    ///
    /// # Example
    /// ```
    /// use heapless::Vec;
    /// let vec = Vec::from_array([1,2,3]);
    /// assert_eq!(vec.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns the number currently available backup storage.
    ///
    /// this is equal to `self.capacity() - self.len()`
    pub fn available(&self) -> usize {
        self.capacity() - self.len()
    }

    /// Returns `true` if the vector contains no elements.
    ///
    /// # Example
    /// ```
    /// use heapless::Vec;
    /// let vec = Vec::new([0;8]);
    /// assert!(vec.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns `true` if the vector uses the complete backup storage.
    ///
    /// # Example
    /// ```
    /// use heapless::Vec;
    /// let vec = Vec::from_array([1,2,3]);
    /// assert!(vec.is_full());
    /// ```
    pub fn is_full(&self) -> bool {
        self.len() == self.capacity()
    }

    /// Clears the vector, removing all values.
    ///
    /// `v.truncate(0)` has the same effect as `v.clear()`.
    /// # Example
    /// ```
    /// use heapless::Vec;
    /// let mut vec = Vec::from_array([0,1,2,3]);
    /// vec.clear();
    /// assert_eq!(vec.as_slice(), &[]);
    /// ```
    pub fn clear(&mut self) {
        self.truncate(0);
    }

    /// Removes the last element from this vector and returns it, or `None` if
    /// it's empty.
    ///
    /// # Example
    /// ```
    /// use heapless::Vec;
    /// let mut vec = Vec::from_array([1,2]);
    /// assert_eq!(vec.pop(), Some(2));
    /// assert_eq!(vec.pop(), Some(1));
    /// assert_eq!(vec.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            let len = self.len();
            unsafe {
                self.set_len(len - 1);
            }
            Some(self.array.as_ref()[len - 1])
        }
    }

    /// Appends an `elem`ent to the back of the collection
    ///
    /// This method returns `Err(element)` if the vector is full.
    pub fn push(&mut self, element: T) -> Result<(), T> {
        if self.is_full() {
            Err(element)
        } else {
            let len = self.len();
            {
                let slice = self.array.as_mut();
                slice[len] = element;
            }
            unsafe {
                self.set_len(len + 1);
            }
            Ok(())
        }
    }

    /// Removes an element from the vector and returns it.
    /// The removed element is replaced by the last element of the vector.
    ///
    /// # Panics
    /// Panics if index is out of bounds.
    ///
    /// # Example
    /// ```
    /// use heapless::Vec;
    /// let mut vec = Vec::from_array([0, 1, 2, 3]);
    /// assert_eq!(vec.swap_remove(2), 2);
    /// assert_eq!(vec.as_slice(), &[0, 1, 3]);
    /// ```
    pub fn swap_remove(&mut self, index: usize) -> T {
        let last = self.len() - 1;
        self.as_mut_slice().swap(index, last);
        self.pop().unwrap() // safe here, as we cant swap if len == 0
    }

    /// Inserts an element at position `index` within the vector, shifting all
    /// elements after it to the right.
    ///
    /// Returns Err(element) if backup storage is full.
    ///
    /// # Panics
    /// Panics if `index` is out of bounds.
    ///
    /// # Example
    /// ```
    /// use heapless::Vec;
    /// let mut vec = Vec::new([0;8]);
    /// assert!(vec.push(1).is_ok());
    /// assert!(vec.push(2).is_ok());
    /// assert!(vec.insert(1, 10).is_ok());
    /// assert_eq!(vec.as_slice(), &[1, 10, 2]);
    /// ```
    pub fn insert(&mut self, index: usize, element: T) -> Result<(), T> {
        if self.is_full() {
            return Err(element);
        }
        let len = self.len();
        assert!(index <= len);
        unsafe {
            // infallible
            // The spot to put the new value
            {
                let p = self.as_mut_ptr().offset(index as isize);
                // Shift everything over to make space. (Duplicating the
                // `index`th element into two consecutive places.)
                ptr::copy(p, p.offset(1), len - index);
                // Write it in, overwriting the first copy of the `index`th
                // element.
                ptr::write(p, element);
                self.set_len(len + 1);
            }
        }
        Ok(())
    }

    /// Copies all the elements of `other` into the vector.
    ///
    /// Does not insert any elements into the vector
    /// if it could not hold all of them.
    /// Use `vec.append_force(&other)` to force insertion.
    ///
    /// # Example
    /// ```
    /// use heapless::Vec;
    /// let mut vec = Vec::new([0;16]);
    /// let other = [3, 4];
    /// assert!(vec.push(1).is_ok());
    /// assert!(vec.push(2).is_ok());
    /// assert!(vec.append(&other).is_ok());
    /// assert_eq!(vec.as_slice(), &[1, 2, 3, 4]);
    /// ```
    pub fn append<S>(&mut self, other: &S) -> Result<(), ()>
    where
        S: AsRef<[T]>,
    {
        if self.available() < other.as_ref().len() {
            return Err(());
        }
        // FIXME: use mem::copy instead of iter.cloned()
        for x in other.as_ref().iter().cloned() {
            match self.push(x) {
                Ok(_) => {}
                // Error can not occure as available length was checked
                _ => unreachable!(),
            }
        }
        Ok(())
    }

    /// Copies as much elements of `other` into the vector as possible.
    ///
    /// Returns Err(rest) if not all elements could be inserted.
    /// `rest` is the remaining slice.
    /// Use `vec.append(&other)` if other is known to fit into self.
    /// # Example
    /// ```
    /// use heapless::Vec;
    /// let mut vec = Vec::new([0;4]);
    /// let other = [3, 4, 5];
    /// assert!(vec.push(1).is_ok());
    /// assert!(vec.push(2).is_ok());
    /// assert_eq!(vec.append_force(&other), Err([5].as_ref()));
    /// assert_eq!(vec.as_slice(), &[1, 2, 3, 4]);
    /// ```
    pub fn append_force<'a, S>(&mut self, other: &'a S) -> Result<(), &'a [T]>
    where
        S: AsRef<[T]>,
    {
        let to_insert = cmp::min(self.available(), other.as_ref().len());
        // FIXME: use mem::copy instead of iter.cloned()
        for x in other.as_ref().iter().cloned().take(to_insert) {
            match self.push(x) {
                Ok(_) => {}
                // Error can not occure as available length was checked
                _ => unreachable!(),
            }
        }
        if to_insert < other.as_ref().len() {
            return Err(other.as_ref()[to_insert..].as_ref());
        }
        Ok(())
    }

    /// Removes and returns the element at position `index` within the vector,
    /// shifting all elements after it to the left.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Example
    /// ```
    /// use heapless::Vec;
    /// let mut vec = Vec::new([0;8]);
    /// assert!(vec.push(1).is_ok());
    /// assert!(vec.push(2).is_ok());
    /// assert!(vec.push(3).is_ok());
    /// vec.remove(1);
    /// assert_eq!(vec.as_slice(), &[1, 3]);
    /// ```
    pub fn remove(&mut self, index: usize) -> T {
        let len = self.len();
        assert!(index < len);
        unsafe {
            // infallible
            let ret;
            {
                // the place we are taking from.
                let ptr = self.as_mut_ptr().offset(index as isize);
                // copy it out, unsafely having a copy of the value on
                // the stack and in the vector at the same time.
                ret = ptr::read(ptr);
                // Shift everything down to fill in that spot.
                ptr::copy(ptr.offset(1), ptr, len - index - 1);
                self.set_len(len - 1);
            }
            ret
        }
    }

    /// Shortens the vector, keeping the first `len` elements.
    ///
    /// If `len` is greater than the vector's current length, this has no
    /// effect.
    ///
    /// `v.truncate(0)` has the same effect as `v.clear()`.
    ///
    /// # Example
    /// ```
    /// use heapless::Vec;
    /// let mut vec = Vec::from_array([1,2,3,4]);
    /// vec.truncate(2);
    /// assert_eq!(vec.as_slice(), &[1,2]);
    /// ```
    pub fn truncate(&mut self, len: usize) {
        if len <= self.len() {
            unsafe {
                self.set_len(len);
            }
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` where `f(&e)` returns `false`.
    /// This method operates in place and preserves the order of the retained
    /// elements.
    ///
    /// # Example
    /// ```
    /// use heapless::Vec;
    /// let mut vec = Vec::from_array([0, 1, 2, 3]);
    /// vec.retain(|&x| x % 2 == 0);
    /// assert_eq!(vec.as_slice(), &[0, 2]);
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        let len = self.len();
        let mut del = 0;
        {
            let v = self.as_mut_slice();

            for i in 0..len {
                if !f(&v[i]) {
                    del += 1;
                } else if del > 0 {
                    v.swap(i - del, i);
                }
            }
        }
        if del > 0 {
            self.truncate(len - del);
        }
    }

    /// Extracts a slice containing the entire vector.
    /// Equivialent to `v.deref()`
    pub fn as_slice(&self) -> &[T] {
        let len = self.len();
        self.array.as_ref()[..len].as_ref()
    }

    /// Extracts a mutable slice containing the entire vector.
    /// Equivialent to `v.deref_mut()`
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        let len = self.len();
        self.array.as_mut()[..len].as_mut()
    }

    /// Extracts the internaly used storage array.
    ///
    /// This is unsafe because the content of the array behind
    /// the used length is not necessarily valid.
    pub unsafe fn into_inner(self) -> A {
        let Vec {
            _marker: _,
            array,
            len: _,
        } = self;
        array
    }

    /// Sets the length of the vector.
    ///
    /// This is unsafe because ot may expose uninitialized memory
    /// or leak memory. It is not
    pub unsafe fn set_len(&mut self, len: usize) {
        self.len = len;
    }
}

impl<T, A> Deref for Vec<T, A>
where
    A: AsMut<[T]> + AsRef<[T]>,
    T: Copy,
{
    type Target = [T];

    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, A> DerefMut for Vec<T, A>
where
    A: AsMut<[T]> + AsRef<[T]>,
    T: Copy,
{
    fn deref_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

#[cfg(test)]
mod test {

    use core::ops::Deref;
    use core::ops::DerefMut;

    use super::Vec;

    #[test]
    fn deref_mut_reverse() {
        let mut vec = Vec::from_array([1, 2, 3]);
        vec.reverse();
        assert_eq!(vec.as_slice(), &[3, 2, 1]);
    }

    #[test]
    fn compile_time_const_new() {
        const LEN: usize = 16;
        const VEC: Vec<u8, [u8; LEN]> = Vec::new([0; LEN]);
        assert_eq!(VEC.capacity(), LEN);
    }

    #[test]
    fn compile_time_static_new() {
        const LEN: usize = 16;
        static VEC: Vec<u8, [u8; LEN]> = Vec::new([0; LEN]);
        assert_eq!(VEC.capacity(), LEN);
    }

    #[test]
    fn initial_length() {
        const LEN: usize = 16;
        let vec = Vec::new([0; LEN]);
        assert_eq!(vec.len(), 0);
    }

    #[test]
    fn initial_length_from_array() {
        const LEN: usize = 16;
        let vec = Vec::from_array([0; LEN]);
        assert_eq!(vec.capacity(), LEN);
        assert_eq!(vec.len(), LEN);
    }

    #[test]
    fn push_length() {
        const LEN: usize = 16;
        let mut vec = Vec::new([0; LEN]);
        assert!(vec.push(1).is_ok());
        assert_eq!(vec.len(), 1);
    }

    #[test]
    fn push_pop() {
        const LEN: usize = 16;
        let mut vec = Vec::new([0; LEN]);
        assert!(vec.push(1).is_ok());
        assert_eq!(vec.pop(), Some(1));
        assert_eq!(vec.len(), 0);
    }

    #[test]
    fn empty_pop() {
        const LEN: usize = 16;
        let mut vec = Vec::new([0; LEN]);
        assert!(vec.push(1).is_ok());
        assert_eq!(vec.pop(), Some(1));
        assert_eq!(vec.len(), 0);
        assert_eq!(vec.pop(), None);
        assert_eq!(vec.len(), 0);
    }

    #[test]
    fn full_push() {
        const LEN: usize = 2;
        let mut vec = Vec::new([0; LEN]);
        assert!(vec.push(1).is_ok());
        assert!(vec.push(2).is_ok());
        assert_eq!(vec.len(), 2);
        assert!(vec.push(3).is_err());
        assert_eq!(vec.len(), 2);
    }

    #[test]
    fn deref() {
        const LEN: usize = 3;
        let mut vec = Vec::new([0; LEN]);
        assert!(vec.push(1).is_ok());
        assert!(vec.push(2).is_ok());
        assert_eq!(vec.deref(), &[1, 2]);
    }

    #[test]
    fn deref_mut() {
        const LEN: usize = 3;
        let mut vec = Vec::new([0; LEN]);
        assert!(vec.push(1).is_ok());
        assert!(vec.push(2).is_ok());
        vec.deref_mut()[0] = 3;
        vec.deref_mut()[1] = 2;
        assert_eq!(vec.deref(), &[3, 2]);
    }

    #[test]
    fn insert_full() {
        const LEN: usize = 2;
        let mut vec = Vec::new([0; LEN]);
        assert!(vec.push(1).is_ok());
        assert!(vec.push(2).is_ok());
        assert_eq!(vec.insert(1, 10), Err(10));
        assert_eq!(vec.deref(), &[1, 2]);
    }

    /* #[test]
    fn push_pop_non_copy() {
        use core::mem;
        #[derive(Debug, PartialEq, Eq)]
        struct Foo(i32);
        let mut vec = Vec::new([Foo(0), unsafe { mem::uninitialized() }]);
        assert!(vec.push(Foo(1)).is_ok());
        assert_eq!(vec.pop(), Some(Foo(1)));
    } */

    #[test]
    fn with_slice() {
        let mut array = [0_usize; 8];
        let mut vec = Vec::new(&mut array);
        assert!(vec.push(1).is_ok());
        assert_eq!(vec[0], 1);
    }

    #[test]
    fn append_fails() {
        let mut vec = Vec::new([0; 3]);
        let other = [3, 4];
        assert!(vec.push(1).is_ok());
        assert!(vec.push(2).is_ok());
        assert!(vec.append(&other).is_err());
        assert_eq!(vec.as_slice(), &[1, 2]);
    }

}
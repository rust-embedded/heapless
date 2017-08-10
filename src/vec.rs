
#![deny(missing_docs)]
#![deny(warnings)]

use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};
use core::ptr;

use super::OutOfMemoryError;

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
    pub fn from_array(array: A) -> Self {
        let len = array.as_ref().len();
        Vec {
            _marker: PhantomData,
            array: array,
            len: len
        }
    }

    /// Returns the capacity of this vector
    pub fn capacity(&self) -> usize {
        self.array.as_ref().len()
    }

    /// Clears the vector, removing all values
    pub fn clear(&mut self) {
        self.len = 0;
    }

    /// Returns the current length of this vector
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the vector contains no elements.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns `true` if the vector uses the complete backup storage
    pub fn is_full(&self) -> bool {
        self.len() == self.capacity()
    }

    /// Removes the last element from this vector and returns it, or `None` if
    /// it's empty
    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            self.len -= 1;
            Some(self.array.as_ref()[self.len])
        }
    }

    /// Appends an `elem`ent to the back of the collection
    ///
    /// This method returns `Err` if the vector is full
    pub fn push(&mut self, elem: T) -> super::Result<(), T> {
        if self.is_full() {
            Err(OutOfMemoryError::new(elem))
        } else {
            let slice = self.array.as_mut();
            slice[self.len] = elem;
            self.len += 1;
            Ok(())
        }
    }

    /// Swaps two elements in the vector.
    ///
    /// # Arguments
    ///
    /// * a - The index of the first element
    /// * b - The index of the second element
    ///
    /// # Panics
    ///
    /// Panics if `a` or `b` are out of bounds.
    pub fn swap(&mut self, a: usize, b: usize) {
        assert!(a < self.len());
        assert!(b < self.len());
        self.as_mut_slice().swap(a, b)
    }

    /// Removes an element from the vector and returns it.
    /// The removed element is replaced by the last element of the vector.
    ///
    /// # Panics
    /// Panics if index is out of bounds.
    pub fn swap_remove(&mut self, index: usize) -> T {
        let last = self.len() - 1;
        self.swap(index, last);
        self.pop().unwrap() // safe here, as we cant swap if len == 0
    }

    /// Inserts an element at position `index` within the vector, shifting all
    /// elements after it to the right.
    ///
    /// Returns Err((OutOfMemoryError, element)) if backup storage is full.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    pub fn insert(&mut self, index: usize, element: T) -> super::Result<(), T> {
        if self.is_full() {
            return Err(OutOfMemoryError::new(element));
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
            }
            self.len += 1;
        }
        Ok(())
    }

    /// Removes and returns the element at position `index` within the vector,
    /// shifting all elements after it to the left.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
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
            }
            self.len -= 1;
            ret
        }
    }

    /// Shortens the vector, keeping the first `len` elements.
    ///
    /// If `len` is greater than the vector's current length, this has no
    /// effect.
    ///
    /// `v.truncate(0)` has the same effect as `v.clear()`
    pub fn truncate(&mut self, len: usize) {
        if len <= self.len() {
            self.len = len;
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` where `f(&e)` returns `false`.
    /// This method operates in place and preserves the order of the retained
    /// elements.
    pub fn retain<F>(&mut self, mut f: F)
        where F: FnMut(&T) -> bool
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
        self.deref()
    }

    /// Extracts a mutable slice containing the entire vector.
    /// Equivialent to `v.deref_mut()`
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self.deref_mut()
    }

}

impl<T, A> Deref for Vec<T, A>
where
    A: AsMut<[T]> + AsRef<[T]>,
    T: Copy,
{
    type Target = [T];

    fn deref(&self) -> &[T] {
        self.array.as_ref()[..(self.len)].as_ref()
    }
}

impl<T, A> DerefMut for Vec<T, A>
where
    A: AsMut<[T]> + AsRef<[T]>,
    T: Copy,
{

    fn deref_mut(&mut self) -> &mut [T] {
        self.array.as_mut()[..(self.len)].as_mut()
    }
}

#[cfg(test)]
mod test {

    use core::ops::Deref;
    use core::ops::DerefMut;

    use super::Vec;

    #[test]
    fn deref_mut_reverse() {
        let mut vec = Vec::from_array([1,2,3]);
        vec.reverse();
        assert_eq!(vec.as_slice(), &[3,2,1]);
    }
    
    #[test]
    fn compile_time_const_new() {
        const LEN: usize = 16; 
        const VEC: Vec<u8, [u8; LEN]> = Vec::new([0;LEN]);
        assert_eq!(VEC.capacity(), LEN);
    }

    #[test]
    fn compile_time_static_new() {
        const LEN: usize = 16; 
        static VEC: Vec<u8, [u8; LEN]> = Vec::new([0;LEN]);
        assert_eq!(VEC.capacity(), LEN);
    }

    #[test]
    fn initial_length() {
        const LEN: usize = 16; 
        let vec = Vec::new([0;LEN]);
        assert_eq!(vec.len(), 0);
    }

    #[test]
    fn initial_length_from_array() {
        const LEN: usize = 16; 
        let vec = Vec::from_array([0;LEN]);
        assert_eq!(vec.capacity(), LEN);
        assert_eq!(vec.len(), LEN);
    }

    #[test]
    fn push_length() {
        const LEN: usize = 16; 
        let mut vec = Vec::new([0;LEN]);
        assert!(vec.push(1).is_ok());
        assert_eq!(vec.len(), 1);
    }

    #[test]
    fn push_pop() {
        const LEN: usize = 16; 
        let mut vec = Vec::new([0;LEN]);
        assert!(vec.push(1).is_ok());
        assert_eq!(vec.pop(), Some(1));
        assert_eq!(vec.len(), 0);
    }

    #[test]
    fn empty_pop() {
        const LEN: usize = 16; 
        let mut vec = Vec::new([0;LEN]);
        assert!(vec.push(1).is_ok());
        assert_eq!(vec.pop(), Some(1));
        assert_eq!(vec.len(), 0);
        assert_eq!(vec.pop(), None);
        assert_eq!(vec.len(), 0);
    }

    #[test]
    fn full_push() {
        const LEN: usize = 2; 
        let mut vec = Vec::new([0;LEN]);
        assert!(vec.push(1).is_ok());
        assert!(vec.push(2).is_ok());
        assert_eq!(vec.len(), 2);
        assert!(vec.push(3).is_err());
        assert_eq!(vec.len(), 2);
    }

    #[test]
    fn deref() {
        const LEN: usize = 3; 
        let mut vec = Vec::new([0;LEN]);
        assert!(vec.push(1).is_ok());
        assert!(vec.push(2).is_ok());
        assert_eq!(vec.deref(), &[1, 2]);
    }

    #[test]
    fn deref_mut() {
        const LEN: usize = 3; 
        let mut vec = Vec::new([0;LEN]);
        assert!(vec.push(1).is_ok());
        assert!(vec.push(2).is_ok());
        vec.deref_mut()[0] = 3;
        vec.deref_mut()[1] = 2;
        assert_eq!(vec.deref(), &[3,2]);
    }

    #[test]
    fn insert_correctly() {
        const LEN: usize = 16; 
        let mut vec = Vec::new([0;LEN]);
        assert!(vec.push(1).is_ok());
        assert!(vec.push(2).is_ok());
        assert!(vec.insert(1, 10).is_ok());
        assert_eq!(vec.deref(), &[1, 10, 2]);
    }

    #[test]
    fn insert_full() {
        const LEN: usize = 2; 
        let mut vec = Vec::new([0;LEN]);
        assert!(vec.push(1).is_ok());
        assert!(vec.push(2).is_ok());
        assert_eq!(vec.insert(1, 10)
                    .map_err(|e| e.into_inner())
                    .err(),
                  Some(10));
        assert_eq!(vec.deref(), &[1, 2]);
    }

    #[test]
    fn remove() {
        const LEN: usize = 16; 
        let mut vec = Vec::new([0;LEN]);
        assert!(vec.push(1).is_ok());
        assert!(vec.push(2).is_ok());
        assert!(vec.push(3).is_ok());
        vec.remove(1);
        assert_eq!(vec.deref(), &[1, 3]);
    }

    #[test]
    fn swap_remove() {
        let mut vec = Vec::from_array([0, 1, 2, 3]);
        assert_eq!(vec.swap_remove(2), 2);
        assert_eq!(vec.deref(), &[0, 1, 3]);
    }

    #[test]
    fn retain() {
        let mut vec = Vec::from_array([0, 1, 2, 3]);
        vec.retain(|&x| x % 2 == 0);
        assert_eq!(vec.deref(), &[0, 2]);
    }

}
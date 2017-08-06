
#![deny(missing_docs)]
#![deny(warnings)]

use core::marker::PhantomData;
use core::ops::Deref;
use core::slice;

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

    /// Returns the capacity of this vector
    pub fn capacity(&self) -> usize {
        self.array.as_ref().len()
    }

    /// Clears the vector, removing all values
    pub fn clear(&mut self) {
        self.len = 0;
    }

    /// Removes the last element from this vector and returns it, or `None` if
    /// it's empty
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            unsafe { Some(*self.array.as_mut().as_mut_ptr().offset(self.len as isize)) }
        }
    }

    /// Appends an `elem`ent to the back of the collection
    ///
    /// This method returns `Err` if the vector is full
    pub fn push(&mut self, elem: T) -> Result<(), ()> {
        let slice = self.array.as_mut();

        if self.len == slice.len() {
            Err(())
        } else {
            unsafe {
                *slice.as_mut_ptr().offset(self.len as isize) = elem;
            }
            self.len += 1;
            Ok(())
        }
    }
}

impl<T, A> Deref for Vec<T, A>
where
    A: AsMut<[T]> + AsRef<[T]>,
    T: Copy,
{
    type Target = [T];

    fn deref(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.array.as_ref().as_ptr(), self.len) }
    }
}

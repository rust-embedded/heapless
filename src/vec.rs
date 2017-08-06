
#![deny(missing_docs)]
#![deny(warnings)]

use core::marker::PhantomData;
use core::ops::Deref;
use core::ops::DerefMut;

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

    /// Returns the current length of this vector
    pub fn len(&self) -> usize {
        self.len
    }

    /// Removes the last element from this vector and returns it, or `None` if
    /// it's empty
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            Some(self.array.as_ref()[self.len])
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
            slice[self.len] = elem;
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

}
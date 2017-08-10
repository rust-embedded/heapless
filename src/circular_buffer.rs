
#![deny(missing_docs)]
#![deny(warnings)]

use core::marker::PhantomData;
use core::ops::Deref;
use core::slice;

/// A circular buffer
pub struct CircularBuffer<T, A>
where
    A: AsMut<[T]> + AsRef<[T]>,
    T: Copy,
{
    _marker: PhantomData<[T]>,
    array: A,
    index: usize,
    len: usize,
}

impl<T, A> CircularBuffer<T, A>
where
    A: AsMut<[T]> + AsRef<[T]>,
    T: Copy,
{
    /// Creates a new empty circular buffer using `array` as backup storage
    pub const fn new(array: A) -> Self {
        CircularBuffer {
            _marker: PhantomData,
            array: array,
            index: 0,
            len: 0,
        }
    }

    /// Returns the capacity of this buffer
    pub fn capacity(&self) -> usize {
        self.array.as_ref().len()
    }

    /// Pushes `elem`ent into the buffer
    ///
    /// This will overwrite an old value if the buffer is full
    pub fn push(&mut self, elem: T) {
        let slice = self.array.as_mut();
        if self.len < slice.len() {
            self.len += 1;
        }

        unsafe { *slice.as_mut_ptr().offset(self.index as isize) = elem };

        self.index = (self.index + 1) % slice.len();
    }
}

impl<T, A> Deref for CircularBuffer<T, A>
where
    A: AsMut<[T]> + AsRef<[T]>,
    T: Copy,
{
    type Target = [T];

    fn deref(&self) -> &[T] {
        let slice = self.array.as_ref();

        if self.len == slice.len() {
            slice
        } else {
            unsafe { slice::from_raw_parts(slice.as_ptr(), self.len) }
        }
    }
}

#[cfg(test)]
mod test {
    
}

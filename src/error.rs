
#![deny(missing_docs)]
#![deny(warnings)]

use core::result;
use core::borrow::{Borrow, BorrowMut};

/// Error type to indicate that an insertion could not be handeled 
/// due to the backup storage array being full.
/// It constains the rest that could not be inserted into the collection.
pub struct OutOfMemoryError<T>(T);

impl <T> OutOfMemoryError<T> {

    /// Creates a new `OutOfMemoryError` with inner element.
    pub fn new(inner: T) -> Self {
        OutOfMemoryError(inner)
    }

    /// Extracts the inner element and consumes the `OutOfMemoryError`.
    pub fn into_inner(self) -> T {
        self.0
    }

}

impl <T> Borrow<T> for OutOfMemoryError<T> {
    fn borrow(&self) -> &T {
        &self.0
    }
}

impl <T> BorrowMut<T> for OutOfMemoryError<T> {
    fn borrow_mut(&mut self) -> &mut T {
        &mut self.0
    }
}


/// Type alias for short hand usage of `OutOfMemoryError`.
pub type Result<T, R> = result::Result<T, OutOfMemoryError<R>>;

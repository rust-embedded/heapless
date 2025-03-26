//! `Storage` trait defining how data is stored in a container.

use core::borrow::{Borrow, BorrowMut};

pub(crate) trait SealedStorage {
    type Buffer<T>: ?Sized + Borrow<[T]> + BorrowMut<[T]>;
    /// Obtain the length of the buffer
    #[allow(unused)]
    fn len<T>(this: *const Self::Buffer<T>) -> usize;
    /// Obtain access to the first element of the buffer
    #[allow(unused)]
    fn as_ptr<T>(this: *mut Self::Buffer<T>) -> *mut T;
}

/// Trait defining how data for a container is stored.
///
/// There's two implementations available:
///
/// - [`OwnedStorage`]: stores the data in an array `[T; N]` whose size is known at compile time.
/// - [`ViewStorage`]: stores the data in an unsized `[T]`.
///
/// This allows containers to be generic over either sized or unsized storage. For example,
/// the [`vec`](crate::vec) module contains a [`VecInner`](crate::vec::VecInner) struct
/// that's generic on [`Storage`], and two type aliases for convenience:
///
/// - [`Vec<T, N>`](crate::vec::Vec) = `VecInner<T, OwnedStorage<N>>`
/// - [`VecView<T>`](crate::vec::VecView) = `VecInner<T, ViewStorage>`
///
/// `Vec` can be unsized into `VecView`, either by unsizing coercions such as `&mut Vec -> &mut VecView` or
/// `Box<Vec> -> Box<VecView>`, or explicitly with [`.as_view()`](crate::vec::Vec::as_view) or [`.as_mut_view()`](crate::vec::Vec::as_mut_view).
///
/// This trait is sealed, so you cannot implement it for your own types. You can only use
/// the implementations provided by this crate.
#[allow(private_bounds)]
pub trait Storage: SealedStorage {}

/// Implementation of [`Storage`] that stores the data in an array `[T; N]` whose size is known at compile time.
pub enum OwnedStorage<const N: usize> {}
impl<const N: usize> Storage for OwnedStorage<N> {}
impl<const N: usize> SealedStorage for OwnedStorage<N> {
    type Buffer<T> = [T; N];
    fn len<T>(_: *const Self::Buffer<T>) -> usize {
        N
    }
    fn as_ptr<T>(this: *mut Self::Buffer<T>) -> *mut T {
        this.cast()
    }
}

/// Implementation of [`Storage`] that stores the data in an unsized `[T]`.
pub enum ViewStorage {}
impl Storage for ViewStorage {}
impl SealedStorage for ViewStorage {
    type Buffer<T> = [T];
    fn len<T>(this: *const Self::Buffer<T>) -> usize {
        this.len()
    }

    fn as_ptr<T>(this: *mut Self::Buffer<T>) -> *mut T {
        this.cast()
    }
}

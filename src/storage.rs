//! `Storage` trait defining how data is stored in a container.

use core::borrow::{Borrow, BorrowMut};

pub(crate) trait SealedStorage {
    type Buffer<T>: ?Sized + Borrow<[T]> + BorrowMut<[T]>;
}

/// Trait defining how data for a container is stored.
///
/// There's two implementations available:
///
/// - [`OwnedStorage`]: stores the data in an array `[T; N]` whose size is known at compile time.
/// - [`ViewStorage`]: stores the data in an unsized `[T]`.
///
/// This allows containers to be generic over either sized or unsized storage.
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
}

/// Implementation of [`Storage`] that stores the data in an unsized `[T]`.
pub enum ViewStorage {}
impl Storage for ViewStorage {}
impl SealedStorage for ViewStorage {
    type Buffer<T> = [T];
}

//! `Storage` trait defining how data is stored in a container.

use core::borrow::{Borrow, BorrowMut};

#[cfg(any(
    feature = "portable-atomic",
    all(feature = "mpmc_large", target_has_atomic = "ptr"),
    all(not(feature = "mpmc_large"), target_has_atomic = "8")
))]
use crate::mpmc::{MpMcQueueInner, MpMcQueueView};
#[cfg(any(
    feature = "portable-atomic",
    target_has_atomic = "ptr",
    has_atomic_load_store
))]
use crate::spsc::{QueueInner, QueueView};
use crate::{
    binary_heap::{BinaryHeapInner, BinaryHeapView},
    deque::{DequeInner, DequeView},
    histbuf::{HistoryBufferInner, HistoryBufferView},
    linear_map::{LinearMapInner, LinearMapView},
    sorted_linked_list::{SortedLinkedListIndex, SortedLinkedListInner, SortedLinkedListView},
    string::{StringInner, StringView},
    vec::VecInner,
    VecView,
};

pub(crate) trait SealedStorage: Sized {
    type Buffer<T>: ?Sized + Borrow<[T]> + BorrowMut<[T]>;
    /// Obtain the length of the buffer
    #[allow(unused)]
    fn len<T>(this: *const Self::Buffer<T>) -> usize;
    /// Obtain access to the first element of the buffer
    #[allow(unused)]
    fn as_ptr<T>(this: *mut Self::Buffer<T>) -> *mut T;

    /// Convert a `Vec` to a `VecView`
    fn as_vec_view<T>(this: &VecInner<T, Self>) -> &VecView<T>
    where
        Self: Storage;
    /// Convert a `Vec` to a `VecView`
    fn as_mut_vec_view<T>(this: &mut VecInner<T, Self>) -> &mut VecView<T>
    where
        Self: Storage;
    /// Convert a `HistoryBuffer` to a `HistoryBufferView`
    fn as_histbuf_view<T>(this: &HistoryBufferInner<T, Self>) -> &HistoryBufferView<T>
    where
        Self: Storage;
    /// Convert a `HistoryBuffer` to a `HistoryBufferView`
    fn as_mut_histbuf_view<T>(this: &mut HistoryBufferInner<T, Self>) -> &mut HistoryBufferView<T>
    where
        Self: Storage;
    #[cfg(any(
        feature = "portable-atomic",
        all(feature = "mpmc_large", target_has_atomic = "ptr"),
        all(not(feature = "mpmc_large"), target_has_atomic = "8")
    ))]
    /// Convert a `MpMcQueue` to a `MpMcQueueView`
    fn as_mpmc_queue_view<T>(this: &MpMcQueueInner<T, Self>) -> &MpMcQueueView<T>
    where
        Self: Storage;
    #[cfg(any(
        feature = "portable-atomic",
        all(feature = "mpmc_large", target_has_atomic = "ptr"),
        all(not(feature = "mpmc_large"), target_has_atomic = "8")
    ))]
    /// Convert a `MpMcQueue` to a `MpMcQueueView`
    fn as_mut_mpmc_queue_view<T>(this: &mut MpMcQueueInner<T, Self>) -> &mut MpMcQueueView<T>
    where
        Self: Storage;
    /// Convert a `LinearMap` to a `LinearMapView`
    fn as_linear_map_view<K, V>(this: &LinearMapInner<K, V, Self>) -> &LinearMapView<K, V>
    where
        Self: Storage;
    /// Convert a `LinearMap` to a `LinearMapView`
    fn as_mut_linear_map_view<K, V>(
        this: &mut LinearMapInner<K, V, Self>,
    ) -> &mut LinearMapView<K, V>
    where
        Self: Storage;
    /// Convert a `BinaryHeap` to a `BinaryHeapView`
    fn as_binary_heap_view<T, K>(this: &BinaryHeapInner<T, K, Self>) -> &BinaryHeapView<T, K>
    where
        Self: Storage;
    /// Convert a `BinaryHeap` to a `BinaryHeapView`
    fn as_mut_binary_heap_view<T, K>(
        this: &mut BinaryHeapInner<T, K, Self>,
    ) -> &mut BinaryHeapView<T, K>
    where
        Self: Storage;
    #[cfg(any(
        feature = "portable-atomic",
        target_has_atomic = "ptr",
        has_atomic_load_store
    ))]
    /// Convert a `Queue` to a `QueueView`
    fn as_queue_view<T>(this: &QueueInner<T, Self>) -> &QueueView<T>
    where
        Self: Storage;
    #[cfg(any(
        feature = "portable-atomic",
        target_has_atomic = "ptr",
        has_atomic_load_store
    ))]
    /// Convert a `Queue` to a `QueueView`
    fn as_mut_queue_view<T>(this: &mut QueueInner<T, Self>) -> &mut QueueView<T>
    where
        Self: Storage;
    /// Convert a `Deque` to a `DequeView`
    fn as_deque_view<T>(this: &DequeInner<T, Self>) -> &DequeView<T>
    where
        Self: Storage;
    /// Convert a `Deque` to a `DequeView`
    fn as_mut_deque_view<T>(this: &mut DequeInner<T, Self>) -> &mut DequeView<T>
    where
        Self: Storage;
    /// Convert a `String` to a `StringView`
    fn as_string_view(this: &StringInner<Self>) -> &StringView
    where
        Self: Storage;
    /// Convert a `String` to a `StringView`
    fn as_mut_string_view(this: &mut StringInner<Self>) -> &mut StringView
    where
        Self: Storage;
    /// Convert a `SortedLinkedList` to a `SortedLinkedListView`
    fn as_sorted_linked_list_view<T, Idx: SortedLinkedListIndex, K>(
        this: &SortedLinkedListInner<T, Idx, K, Self>,
    ) -> &SortedLinkedListView<T, Idx, K>
    where
        Self: Storage;
    /// Convert a `SortedLinkedList` to a `SortedLinkedListView`
    fn as_mut_sorted_linked_list_view<T, Idx: SortedLinkedListIndex, K>(
        this: &mut SortedLinkedListInner<T, Idx, K, Self>,
    ) -> &mut SortedLinkedListView<T, Idx, K>
    where
        Self: Storage;
}

/// Trait defining how data for a container is stored.
///
/// There's two implementations available:
///
/// - [`OwnedStorage`]: stores the data in an array `[T; N]` whose size is known at compile time.
/// - [`ViewStorage`]: stores the data in an unsized `[T]`.
///
/// This allows containers to be generic over either sized or unsized storage. For example,
/// the [`vec`](crate::vec) module contains a [`VecInner`] struct
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
        this as _
    }
    /// Convert a `Vec` to a `VecView`
    fn as_vec_view<T>(this: &VecInner<T, Self>) -> &VecView<T> {
        this
    }
    /// Convert a `Vec` to a `VecView`
    fn as_mut_vec_view<T>(this: &mut VecInner<T, Self>) -> &mut VecView<T> {
        this
    }
    /// Convert a `SortedLinkedList` to a `SortedLinkedListView`
    fn as_sorted_linked_list_view<T, Idx: SortedLinkedListIndex, K>(
        this: &SortedLinkedListInner<T, Idx, K, Self>,
    ) -> &SortedLinkedListView<T, Idx, K> {
        this
    }
    /// Convert a `SortedLinkedList` to a `SortedLinkedListView`
    fn as_mut_sorted_linked_list_view<T, Idx: SortedLinkedListIndex, K>(
        this: &mut SortedLinkedListInner<T, Idx, K, Self>,
    ) -> &mut SortedLinkedListView<T, Idx, K> {
        this
    }
    #[cfg(any(
        feature = "portable-atomic",
        target_has_atomic = "ptr",
        has_atomic_load_store
    ))]
    /// Convert a `Queue` to a `QueueView`
    fn as_queue_view<T>(this: &QueueInner<T, Self>) -> &QueueView<T> {
        this
    }
    #[cfg(any(
        feature = "portable-atomic",
        target_has_atomic = "ptr",
        has_atomic_load_store
    ))]
    /// Convert a `Queue` to a `QueueView`
    fn as_mut_queue_view<T>(this: &mut QueueInner<T, Self>) -> &mut QueueView<T> {
        this
    }
    /// Convert a `Deque` to a `DequeView`
    fn as_deque_view<T>(this: &DequeInner<T, Self>) -> &DequeView<T> {
        this
    }
    /// Convert a `Deque` to a `DequeView`
    fn as_mut_deque_view<T>(this: &mut DequeInner<T, Self>) -> &mut DequeView<T> {
        this
    }
    /// Convert a `String` to a `StringView`
    fn as_string_view(this: &StringInner<Self>) -> &StringView {
        this
    }
    /// Convert a `String` to a `StringView`
    fn as_mut_string_view(this: &mut StringInner<Self>) -> &mut StringView {
        this
    }
    /// Convert a `LinearMap` to a `LinearMapView`
    fn as_linear_map_view<K, V>(this: &LinearMapInner<K, V, Self>) -> &LinearMapView<K, V> {
        this
    }
    /// Convert a `LinearMap` to a `LinearMapView`
    fn as_mut_linear_map_view<K, V>(
        this: &mut LinearMapInner<K, V, Self>,
    ) -> &mut LinearMapView<K, V> {
        this
    }
    #[cfg(any(
        feature = "portable-atomic",
        all(feature = "mpmc_large", target_has_atomic = "ptr"),
        all(not(feature = "mpmc_large"), target_has_atomic = "8")
    ))]
    /// Convert a `MpMcQueue` to a `MpMcQueueView`
    fn as_mpmc_queue_view<T>(this: &MpMcQueueInner<T, Self>) -> &MpMcQueueView<T> {
        this
    }
    #[cfg(any(
        feature = "portable-atomic",
        all(feature = "mpmc_large", target_has_atomic = "ptr"),
        all(not(feature = "mpmc_large"), target_has_atomic = "8")
    ))]
    /// Convert a `MpMcQueue` to a `MpMcQueueView`
    fn as_mut_mpmc_queue_view<T>(this: &mut MpMcQueueInner<T, Self>) -> &mut MpMcQueueView<T> {
        this
    }
    fn as_binary_heap_view<T, K>(this: &BinaryHeapInner<T, K, Self>) -> &BinaryHeapView<T, K> {
        this
    }
    /// Convert a `BinaryHeap` to a `BinaryHeapView`
    fn as_mut_binary_heap_view<T, K>(
        this: &mut BinaryHeapInner<T, K, Self>,
    ) -> &mut BinaryHeapView<T, K> {
        this
    }
    /// Convert a `HistoryBuffer` to a `HistoryBufferView`
    fn as_histbuf_view<T>(this: &HistoryBufferInner<T, Self>) -> &HistoryBufferView<T> {
        this
    }
    /// Convert a `HistoryBuffer` to a `HistoryBufferView`
    fn as_mut_histbuf_view<T>(this: &mut HistoryBufferInner<T, Self>) -> &mut HistoryBufferView<T> {
        this
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
        this as _
    }
    /// Convert a `Vec` to a `VecView`
    fn as_vec_view<T>(this: &VecInner<T, Self>) -> &VecView<T> {
        this
    }
    /// Convert a `Vec` to a `VecView`
    fn as_mut_vec_view<T>(this: &mut VecInner<T, Self>) -> &mut VecView<T> {
        this
    }
    /// Convert a `SortedLinkedList` to a `SortedLinkedListView`
    fn as_sorted_linked_list_view<T, Idx: SortedLinkedListIndex, K>(
        this: &SortedLinkedListInner<T, Idx, K, Self>,
    ) -> &SortedLinkedListView<T, Idx, K> {
        this
    }
    /// Convert a `SortedLinkedList` to a `SortedLinkedListView`
    fn as_mut_sorted_linked_list_view<T, Idx: SortedLinkedListIndex, K>(
        this: &mut SortedLinkedListInner<T, Idx, K, Self>,
    ) -> &mut SortedLinkedListView<T, Idx, K> {
        this
    }
    #[cfg(any(
        feature = "portable-atomic",
        target_has_atomic = "ptr",
        has_atomic_load_store
    ))]
    /// Convert a `Queue` to a `QueueView`
    fn as_queue_view<T>(this: &QueueInner<T, Self>) -> &QueueView<T> {
        this
    }
    #[cfg(any(
        feature = "portable-atomic",
        target_has_atomic = "ptr",
        has_atomic_load_store
    ))]
    /// Convert a `Queue` to a `QueueView`
    fn as_mut_queue_view<T>(this: &mut QueueInner<T, Self>) -> &mut QueueView<T> {
        this
    }
    /// Convert a `Deque` to a `DequeView`
    fn as_deque_view<T>(this: &DequeInner<T, Self>) -> &DequeView<T> {
        this
    }
    /// Convert a `Deque` to a `DequeView`
    fn as_mut_deque_view<T>(this: &mut DequeInner<T, Self>) -> &mut DequeView<T> {
        this
    }
    /// Convert a `String` to a `StringView`
    fn as_string_view(this: &StringInner<Self>) -> &StringView {
        this
    }
    /// Convert a `String` to a `StringView`
    fn as_mut_string_view(this: &mut StringInner<Self>) -> &mut StringView {
        this
    }
    /// Convert a `LinearMap` to a `LinearMapView`
    fn as_linear_map_view<K, V>(this: &LinearMapInner<K, V, Self>) -> &LinearMapView<K, V> {
        this
    }
    /// Convert a `LinearMap` to a `LinearMapView`
    fn as_mut_linear_map_view<K, V>(
        this: &mut LinearMapInner<K, V, Self>,
    ) -> &mut LinearMapView<K, V> {
        this
    }
    #[cfg(any(
        feature = "portable-atomic",
        all(feature = "mpmc_large", target_has_atomic = "ptr"),
        all(not(feature = "mpmc_large"), target_has_atomic = "8")
    ))]
    /// Convert a `MpMcQueue` to a `MpMcQueueView`
    fn as_mpmc_queue_view<T>(this: &MpMcQueueInner<T, Self>) -> &MpMcQueueView<T> {
        this
    }
    #[cfg(any(
        feature = "portable-atomic",
        all(feature = "mpmc_large", target_has_atomic = "ptr"),
        all(not(feature = "mpmc_large"), target_has_atomic = "8")
    ))]
    /// Convert a `MpMcQueue` to a `MpMcQueueView`
    fn as_mut_mpmc_queue_view<T>(this: &mut MpMcQueueInner<T, Self>) -> &mut MpMcQueueView<T> {
        this
    }
    fn as_binary_heap_view<T, K>(this: &BinaryHeapInner<T, K, Self>) -> &BinaryHeapView<T, K> {
        this
    }
    /// Convert a `BinaryHeap` to a `BinaryHeapView`
    fn as_mut_binary_heap_view<T, K>(
        this: &mut BinaryHeapInner<T, K, Self>,
    ) -> &mut BinaryHeapView<T, K> {
        this
    }
    /// Convert a `HistoryBuffer` to a `HistoryBufferView`
    fn as_histbuf_view<T>(this: &HistoryBufferInner<T, Self>) -> &HistoryBufferView<T> {
        this
    }
    /// Convert a `HistoryBuffer` to a `HistoryBufferView`
    fn as_mut_histbuf_view<T>(this: &mut HistoryBufferInner<T, Self>) -> &mut HistoryBufferView<T> {
        this
    }
}

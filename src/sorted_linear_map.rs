//! A fixed capacity map/dictionary that keeps entries sorted by key and
//! performs lookups via binary search.
//!
//! This is to [`LinearMap`](crate::LinearMap) what `BTreeMap` is to `HashMap`: lookups are
//! *O*(log n) instead of *O*(n), and iteration yields entries in key order. Insertions and
//! removals still require *O*(n) time because the underlying storage is a contiguous array and
//! elements must be shifted to maintain sort order.

use core::{
    borrow::Borrow,
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    iter::FusedIterator,
    mem,
    ops::{self, Bound, RangeBounds},
    slice,
};

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

use crate::vec::{OwnedVecStorage, Vec, VecInner, ViewVecStorage};

mod storage {
    use crate::vec::{OwnedVecStorage, VecStorage, ViewVecStorage};

    use super::{SortedLinearMapInner, SortedLinearMapView};

    /// Trait defining how data for a [`SortedLinearMap`](super::SortedLinearMap) is stored.
    ///
    /// There's two implementations available:
    ///
    /// - [`OwnedStorage`]: stores the data in an array whose size is known at compile time.
    /// - [`ViewStorage`]: stores the data in an unsized slice.
    ///
    /// This allows [`SortedLinearMap`] to be generic over either sized or unsized storage. The
    /// [`sorted_linear_map`](super) module contains a [`SortedLinearMapInner`] struct that's
    /// generic on [`SortedLinearMapStorage`], and two type aliases for convenience:
    ///
    /// - [`SortedLinearMap<K, V, N>`](super::SortedLinearMap) = `SortedLinearMapInner<K, V,
    ///   OwnedStorage<K, V, N>>`
    /// - [`SortedLinearMapView<K, V>`](super::SortedLinearMapView) = `SortedLinearMapInner<K, V,
    ///   ViewStorage<K, V>>`
    ///
    /// `SortedLinearMap` can be unsized into `SortedLinearMapView`, either by unsizing coercions
    /// such as `&mut SortedLinearMap -> &mut SortedLinearMapView` or `Box<SortedLinearMap> ->
    /// Box<SortedLinearMapView>`, or explicitly with
    /// [`.as_view()`](super::SortedLinearMap::as_view) or
    /// [`.as_mut_view()`](super::SortedLinearMap::as_mut_view).
    ///
    /// This trait is sealed, so you cannot implement it for your own types. You can only use
    /// the implementations provided by this crate.
    ///
    /// [`SortedLinearMapInner`]: super::SortedLinearMapInner
    /// [`SortedLinearMap`]: super::SortedLinearMap
    /// [`OwnedStorage`]: super::OwnedStorage
    /// [`ViewStorage`]: super::ViewStorage
    pub trait SortedLinearMapStorage<K, V>: SortedLinearMapStorageSealed<K, V> {}
    pub trait SortedLinearMapStorageSealed<K, V>: VecStorage<(K, V)> {
        fn as_sorted_linear_map_view(
            this: &SortedLinearMapInner<K, V, Self>,
        ) -> &SortedLinearMapView<K, V>
        where
            Self: SortedLinearMapStorage<K, V>;
        fn as_sorted_linear_map_mut_view(
            this: &mut SortedLinearMapInner<K, V, Self>,
        ) -> &mut SortedLinearMapView<K, V>
        where
            Self: SortedLinearMapStorage<K, V>;
    }

    impl<K, V, const N: usize> SortedLinearMapStorage<K, V> for OwnedVecStorage<(K, V), N> {}
    impl<K, V, const N: usize> SortedLinearMapStorageSealed<K, V> for OwnedVecStorage<(K, V), N> {
        fn as_sorted_linear_map_view(
            this: &SortedLinearMapInner<K, V, Self>,
        ) -> &SortedLinearMapView<K, V>
        where
            Self: SortedLinearMapStorage<K, V>,
        {
            this
        }
        fn as_sorted_linear_map_mut_view(
            this: &mut SortedLinearMapInner<K, V, Self>,
        ) -> &mut SortedLinearMapView<K, V>
        where
            Self: SortedLinearMapStorage<K, V>,
        {
            this
        }
    }

    impl<K, V> SortedLinearMapStorage<K, V> for ViewVecStorage<(K, V)> {}

    impl<K, V> SortedLinearMapStorageSealed<K, V> for ViewVecStorage<(K, V)> {
        fn as_sorted_linear_map_view(
            this: &SortedLinearMapInner<K, V, Self>,
        ) -> &SortedLinearMapView<K, V>
        where
            Self: SortedLinearMapStorage<K, V>,
        {
            this
        }
        fn as_sorted_linear_map_mut_view(
            this: &mut SortedLinearMapInner<K, V, Self>,
        ) -> &mut SortedLinearMapView<K, V>
        where
            Self: SortedLinearMapStorage<K, V>,
        {
            this
        }
    }
}

pub use storage::SortedLinearMapStorage;
/// Implementation of [`SortedLinearMapStorage`] that stores the data in an array whose size is
/// known at compile time.
pub type OwnedStorage<K, V, const N: usize> = OwnedVecStorage<(K, V), N>;
/// Implementation of [`SortedLinearMapStorage`] that stores the data in an unsized slice.
pub type ViewStorage<K, V> = ViewVecStorage<(K, V)>;

/// Base struct for [`SortedLinearMap`] and [`SortedLinearMapView`].
#[cfg_attr(
    feature = "zeroize",
    derive(Zeroize),
    zeroize(bound = "S: Zeroize, K: Zeroize, V: Zeroize")
)]
pub struct SortedLinearMapInner<K, V, S: SortedLinearMapStorage<K, V> + ?Sized> {
    pub(crate) buffer: VecInner<(K, V), usize, S>,
}

/// A fixed capacity map/dictionary whose entries are kept sorted by key.
///
/// Lookups use binary search, so `get`, `contains_key`, and similar operations run in
/// *O*(log n) time. Insertions and removals are *O*(n) because the underlying storage is a
/// contiguous array and elements must be shifted to preserve the sort order. Iteration yields
/// entries in ascending key order.
pub type SortedLinearMap<K, V, const N: usize> = SortedLinearMapInner<K, V, OwnedStorage<K, V, N>>;

/// A dynamic capacity map/dictionary whose entries are kept sorted by key.
///
/// See [`SortedLinearMap`] for the characteristics of the underlying operations.
pub type SortedLinearMapView<K, V> = SortedLinearMapInner<K, V, ViewStorage<K, V>>;

impl<K, V, const N: usize> SortedLinearMap<K, V, N> {
    /// Creates an empty `SortedLinearMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::SortedLinearMap;
    ///
    /// // allocate the map on the stack
    /// let mut map: SortedLinearMap<&str, isize, 8> = SortedLinearMap::new();
    ///
    /// // allocate the map in a static variable
    /// static mut MAP: SortedLinearMap<&str, isize, 8> = SortedLinearMap::new();
    /// ```
    pub const fn new() -> Self {
        Self { buffer: Vec::new() }
    }
}

impl<K, V, S: SortedLinearMapStorage<K, V> + ?Sized> SortedLinearMapInner<K, V, S>
where
    K: Ord,
{
    /// Get a reference to the `SortedLinearMap`, erasing the `N` const-generic.
    pub fn as_view(&self) -> &SortedLinearMapView<K, V> {
        S::as_sorted_linear_map_view(self)
    }

    /// Get a mutable reference to the `SortedLinearMap`, erasing the `N` const-generic.
    pub fn as_mut_view(&mut self) -> &mut SortedLinearMapView<K, V> {
        S::as_sorted_linear_map_mut_view(self)
    }

    /// Returns the number of elements that the map can hold.
    ///
    /// Computes in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::SortedLinearMap;
    ///
    /// let map: SortedLinearMap<&str, isize, 8> = SortedLinearMap::new();
    /// assert_eq!(map.capacity(), 8);
    /// ```
    pub fn capacity(&self) -> usize {
        self.buffer.capacity()
    }

    /// Clears the map, removing all key-value pairs.
    ///
    /// Computes in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::SortedLinearMap;
    ///
    /// let mut map: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
    /// map.insert(1, "a").unwrap();
    /// map.clear();
    /// assert!(map.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.buffer.clear();
    }

    /// Returns `true` if the map contains a value for the specified key.
    ///
    /// Computes in *O*(log n) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::SortedLinearMap;
    ///
    /// let mut map: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
    /// map.insert(1, "a").unwrap();
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.binary_search(key).is_ok()
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// Computes in *O*(log n) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::SortedLinearMap;
    ///
    /// let mut map: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
    /// map.insert(1, "a").unwrap();
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.binary_search(key).ok().map(|idx| &self.buffer[idx].1)
    }

    /// Returns a reference to the key-value pair corresponding to the supplied key.
    ///
    /// Computes in *O*(log n) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::SortedLinearMap;
    ///
    /// let mut map: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
    /// map.insert(1, "a").unwrap();
    /// assert_eq!(map.get_key_value(&1), Some((&1, &"a")));
    /// assert_eq!(map.get_key_value(&2), None);
    /// ```
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.binary_search(key).ok().map(|idx| {
            let (k, v) = &self.buffer[idx];
            (k, v)
        })
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// Computes in *O*(log n) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::SortedLinearMap;
    ///
    /// let mut map: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
    /// map.insert(1, "a").unwrap();
    /// if let Some(x) = map.get_mut(&1) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map[&1], "b");
    /// ```
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        match self.binary_search(key) {
            Ok(idx) => Some(&mut self.buffer.as_mut_slice()[idx].1),
            Err(_) => None,
        }
    }

    /// Returns the first key-value pair in the map, or `None` if the map is empty.
    ///
    /// The returned pair is the one with the smallest key.
    ///
    /// Computes in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::SortedLinearMap;
    ///
    /// let mut map: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
    /// assert!(map.first_key_value().is_none());
    /// map.insert(2, "b").unwrap();
    /// map.insert(1, "a").unwrap();
    /// assert_eq!(map.first_key_value(), Some((&1, &"a")));
    /// ```
    pub fn first_key_value(&self) -> Option<(&K, &V)> {
        self.buffer.first().map(|(k, v)| (k, v))
    }

    /// Returns the last key-value pair in the map, or `None` if the map is empty.
    ///
    /// The returned pair is the one with the largest key.
    ///
    /// Computes in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::SortedLinearMap;
    ///
    /// let mut map: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
    /// map.insert(2, "b").unwrap();
    /// map.insert(1, "a").unwrap();
    /// assert_eq!(map.last_key_value(), Some((&2, &"b")));
    /// ```
    pub fn last_key_value(&self) -> Option<(&K, &V)> {
        self.buffer.last().map(|(k, v)| (k, v))
    }

    /// Removes and returns the first key-value pair in the map.
    ///
    /// The returned pair is the one with the smallest key. Returns `None` if the map is empty.
    ///
    /// Computes in *O*(n) time because the remaining entries must be shifted.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::SortedLinearMap;
    ///
    /// let mut map: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
    /// map.insert(2, "b").unwrap();
    /// map.insert(1, "a").unwrap();
    /// assert_eq!(map.pop_first(), Some((1, "a")));
    /// assert_eq!(map.pop_first(), Some((2, "b")));
    /// assert_eq!(map.pop_first(), None);
    /// ```
    pub fn pop_first(&mut self) -> Option<(K, V)> {
        if self.buffer.is_empty() {
            None
        } else {
            Some(self.buffer.remove(0))
        }
    }

    /// Removes and returns the last key-value pair in the map.
    ///
    /// The returned pair is the one with the largest key. Returns `None` if the map is empty.
    ///
    /// Computes in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::SortedLinearMap;
    ///
    /// let mut map: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
    /// map.insert(1, "a").unwrap();
    /// map.insert(2, "b").unwrap();
    /// assert_eq!(map.pop_last(), Some((2, "b")));
    /// assert_eq!(map.pop_last(), Some((1, "a")));
    /// assert_eq!(map.pop_last(), None);
    /// ```
    pub fn pop_last(&mut self) -> Option<(K, V)> {
        self.buffer.pop()
    }

    /// Returns the number of elements in this map.
    ///
    /// Computes in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::SortedLinearMap;
    ///
    /// let mut a: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(1, "a").unwrap();
    /// assert_eq!(a.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.buffer.len()
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old value is returned.
    /// The key is not updated in that case.
    ///
    /// Computes in *O*(n) time in the worst case (binary search is *O*(log n), the shift to
    /// preserve sort order is *O*(n)).
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::SortedLinearMap;
    ///
    /// let mut map: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
    /// assert_eq!(map.insert(37, "a").unwrap(), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(37, "b").unwrap();
    /// assert_eq!(map.insert(37, "c").unwrap(), Some("b"));
    /// assert_eq!(map[&37], "c");
    /// ```
    pub fn insert(&mut self, key: K, mut value: V) -> Result<Option<V>, (K, V)> {
        match self.binary_search(&key) {
            Ok(idx) => {
                let (_, v) = &mut self.buffer.as_mut_slice()[idx];
                mem::swap(v, &mut value);
                Ok(Some(value))
            }
            Err(idx) => match self.buffer.insert(idx, (key, value)) {
                Ok(()) => Ok(None),
                Err((k, v)) => Err((k, v)),
            },
        }
    }

    /// Returns `true` if the map contains no elements.
    ///
    /// Computes in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::SortedLinearMap;
    ///
    /// let mut a: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
    /// assert!(a.is_empty());
    /// a.insert(1, "a").unwrap();
    /// assert!(!a.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns `true` if the map is full.
    ///
    /// Computes in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::SortedLinearMap;
    ///
    /// let mut a: SortedLinearMap<_, _, 4> = SortedLinearMap::new();
    /// assert!(!a.is_full());
    /// a.insert(1, "a").unwrap();
    /// a.insert(2, "b").unwrap();
    /// a.insert(3, "c").unwrap();
    /// a.insert(4, "d").unwrap();
    /// assert!(a.is_full());
    /// ```
    pub fn is_full(&self) -> bool {
        self.len() == self.capacity()
    }

    /// An iterator visiting all key-value pairs in ascending key order.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::SortedLinearMap;
    ///
    /// let mut map: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
    /// map.insert("b", 2).unwrap();
    /// map.insert("a", 1).unwrap();
    /// map.insert("c", 3).unwrap();
    ///
    /// for (key, val) in map.iter() {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            iter: self.buffer.iter(),
        }
    }

    /// An iterator visiting all key-value pairs in ascending key order, with mutable references
    /// to the values.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::SortedLinearMap;
    ///
    /// let mut map: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
    /// map.insert("a", 1).unwrap();
    /// map.insert("b", 2).unwrap();
    /// map.insert("c", 3).unwrap();
    ///
    /// // Update all values
    /// for (_, val) in map.iter_mut() {
    ///     *val = 2;
    /// }
    ///
    /// for (key, val) in &map {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut {
            iter: self.buffer.as_mut_slice().iter_mut(),
        }
    }

    /// An iterator visiting all keys in ascending order.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::SortedLinearMap;
    ///
    /// let mut map: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
    /// map.insert("c", 3).unwrap();
    /// map.insert("a", 1).unwrap();
    /// map.insert("b", 2).unwrap();
    ///
    /// for key in map.keys() {
    ///     println!("{}", key);
    /// }
    /// ```
    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.iter().map(|(k, _)| k)
    }

    /// Removes a key from the map, returning the value at the key if the key was previously in
    /// the map.
    ///
    /// Computes in *O*(n) time because the entries following the removed one must be shifted to
    /// preserve sort order.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::SortedLinearMap;
    ///
    /// let mut map: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
    /// map.insert(1, "a").unwrap();
    /// assert_eq!(map.remove(&1), Some("a"));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        match self.binary_search(key) {
            Ok(idx) => Some(self.buffer.remove(idx).1),
            Err(_) => None,
        }
    }

    /// Removes a key from the map, returning the stored key and value if the key was previously
    /// in the map.
    ///
    /// Computes in *O*(n) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::SortedLinearMap;
    ///
    /// let mut map: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
    /// map.insert(1, "a").unwrap();
    /// assert_eq!(map.remove_entry(&1), Some((1, "a")));
    /// assert_eq!(map.remove_entry(&1), None);
    /// ```
    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        match self.binary_search(key) {
            Ok(idx) => Some(self.buffer.remove(idx)),
            Err(_) => None,
        }
    }

    /// An iterator visiting all values in ascending key order.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::SortedLinearMap;
    ///
    /// let mut map: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
    /// map.insert("c", 3).unwrap();
    /// map.insert("a", 1).unwrap();
    /// map.insert("b", 2).unwrap();
    ///
    /// for val in map.values() {
    ///     println!("{}", val);
    /// }
    /// ```
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.iter().map(|(_, v)| v)
    }

    /// An iterator visiting all values mutably in ascending key order.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::SortedLinearMap;
    ///
    /// let mut map: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
    /// map.insert("a", 1).unwrap();
    /// map.insert("b", 2).unwrap();
    /// map.insert("c", 3).unwrap();
    ///
    /// for val in map.values_mut() {
    ///     *val += 10;
    /// }
    ///
    /// for val in map.values() {
    ///     println!("{}", val);
    /// }
    /// ```
    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut V> {
        self.iter_mut().map(|(_, v)| v)
    }

    /// Returns an iterator over the entries whose keys fall within the given range, in ascending
    /// key order.
    ///
    /// # Panics
    ///
    /// Panics if the supplied range's start is greater than its end, or if the start and end are
    /// equal and both exclusive.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::SortedLinearMap;
    ///
    /// let mut map: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
    /// map.insert(3, "c").unwrap();
    /// map.insert(5, "e").unwrap();
    /// map.insert(8, "h").unwrap();
    ///
    /// let range: heapless::Vec<_, 8> = map.range(4..9).collect();
    /// assert_eq!(&range[..], &[(&5, &"e"), (&8, &"h")]);
    /// ```
    pub fn range<Q, R>(&self, range: R) -> Range<'_, K, V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
        R: RangeBounds<Q>,
    {
        let (start, end) = self.range_indices(range);
        Range {
            iter: self.buffer[start..end].iter(),
        }
    }

    /// Returns a mutable iterator over the entries whose keys fall within the given range, in
    /// ascending key order.
    ///
    /// # Panics
    ///
    /// Panics if the supplied range's start is greater than its end, or if the start and end are
    /// equal and both exclusive.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::SortedLinearMap;
    ///
    /// let mut map: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
    /// map.insert(3, 0).unwrap();
    /// map.insert(5, 0).unwrap();
    /// map.insert(8, 0).unwrap();
    ///
    /// for (_, v) in map.range_mut(4..9) {
    ///     *v = 1;
    /// }
    /// assert_eq!(map.get(&3), Some(&0));
    /// assert_eq!(map.get(&5), Some(&1));
    /// assert_eq!(map.get(&8), Some(&1));
    /// ```
    pub fn range_mut<Q, R>(&mut self, range: R) -> RangeMut<'_, K, V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
        R: RangeBounds<Q>,
    {
        let (start, end) = self.range_indices(range);
        RangeMut {
            iter: self.buffer.as_mut_slice()[start..end].iter_mut(),
        }
    }

    /// Returns an entry for the corresponding key.
    ///
    /// ```
    /// use heapless::sorted_linear_map;
    /// use heapless::SortedLinearMap;
    /// let mut map = SortedLinearMap::<_, _, 16>::new();
    /// if let sorted_linear_map::Entry::Vacant(v) = map.entry("a") {
    ///     v.insert(1).unwrap();
    /// }
    /// if let sorted_linear_map::Entry::Occupied(mut o) = map.entry("a") {
    ///     println!("found {}", *o.get()); // Prints 1
    ///     o.insert(2);
    /// }
    /// // Prints 2
    /// println!("val: {}", *map.get("a").unwrap());
    /// ```
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        match self.binary_search(&key) {
            Ok(idx) => Entry::Occupied(OccupiedEntry {
                idx,
                map: self.as_mut_view(),
            }),
            Err(idx) => Entry::Vacant(VacantEntry {
                idx,
                key,
                map: self.as_mut_view(),
            }),
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all pairs `(k, v)` for which `f(&k, &mut v)` returns `false`. The
    /// elements are visited in ascending key order and the retained entries remain sorted.
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        // Sort order is preserved because `Vec::retain_mut` keeps the relative order of the
        // retained elements.
        self.buffer.retain_mut(|(k, v)| f(k, v));
    }

    fn binary_search<Q>(&self, key: &Q) -> Result<usize, usize>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.buffer.binary_search_by(|(k, _)| k.borrow().cmp(key))
    }

    fn range_indices<Q, R>(&self, range: R) -> (usize, usize)
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
        R: RangeBounds<Q>,
    {
        // Reject obviously invalid ranges up front, matching BTreeMap's panic behavior.
        match (range.start_bound(), range.end_bound()) {
            (Bound::Included(s), Bound::Included(e))
            | (Bound::Included(s), Bound::Excluded(e))
            | (Bound::Excluded(s), Bound::Included(e))
                if s > e =>
            {
                panic!("range start is greater than range end")
            }
            (Bound::Excluded(s), Bound::Excluded(e)) if s >= e => {
                panic!("range start is greater than or equal to range end")
            }
            _ => {}
        }

        let start = match range.start_bound() {
            Bound::Unbounded => 0,
            Bound::Included(k) => match self.binary_search(k) {
                Ok(idx) | Err(idx) => idx,
            },
            Bound::Excluded(k) => match self.binary_search(k) {
                Ok(idx) => idx + 1,
                Err(idx) => idx,
            },
        };
        let end = match range.end_bound() {
            Bound::Unbounded => self.len(),
            Bound::Included(k) => match self.binary_search(k) {
                Ok(idx) => idx + 1,
                Err(idx) => idx,
            },
            Bound::Excluded(k) => match self.binary_search(k) {
                Ok(idx) | Err(idx) => idx,
            },
        };
        (start, end)
    }
}

impl<K, V, Q, S: SortedLinearMapStorage<K, V> + ?Sized> ops::Index<&'_ Q>
    for SortedLinearMapInner<K, V, S>
where
    K: Borrow<Q> + Ord,
    Q: Ord + ?Sized,
{
    type Output = V;

    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("no entry found for key")
    }
}

impl<K, V, Q, S: SortedLinearMapStorage<K, V> + ?Sized> ops::IndexMut<&'_ Q>
    for SortedLinearMapInner<K, V, S>
where
    K: Borrow<Q> + Ord,
    Q: Ord + ?Sized,
{
    fn index_mut(&mut self, key: &Q) -> &mut V {
        self.get_mut(key).expect("no entry found for key")
    }
}

impl<K, V, const N: usize> Default for SortedLinearMap<K, V, N>
where
    K: Ord,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V, const N: usize> Clone for SortedLinearMap<K, V, N>
where
    K: Ord + Clone,
    V: Clone,
{
    fn clone(&self) -> Self {
        Self {
            buffer: self.buffer.clone(),
        }
    }
}

impl<K, V, S: SortedLinearMapStorage<K, V> + ?Sized> fmt::Debug for SortedLinearMapInner<K, V, S>
where
    K: Ord + fmt::Debug,
    V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, V, const N: usize> FromIterator<(K, V)> for SortedLinearMap<K, V, N>
where
    K: Ord,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (K, V)>,
    {
        let mut out = Self::new();
        for (k, v) in iter {
            let _ = out.insert(k, v);
        }
        out
    }
}

/// An iterator that moves out of a [`SortedLinearMap`].
///
/// This struct is created by calling the [`into_iter`](SortedLinearMap::into_iter) method on
/// [`SortedLinearMap`].
pub struct IntoIter<K, V, const N: usize>
where
    K: Ord,
{
    inner: <Vec<(K, V), N, usize> as IntoIterator>::IntoIter,
}

impl<K, V, const N: usize> Iterator for IntoIter<K, V, N>
where
    K: Ord,
{
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl<K, V, const N: usize> FusedIterator for IntoIter<K, V, N> where K: Ord {}

impl<K, V, const N: usize> ExactSizeIterator for IntoIter<K, V, N>
where
    K: Ord,
{
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K, V, const N: usize> IntoIterator for SortedLinearMap<K, V, N>
where
    K: Ord,
{
    type Item = (K, V);
    type IntoIter = IntoIter<K, V, N>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.buffer.into_iter(),
        }
    }
}

impl<'a, K, V, S: SortedLinearMapStorage<K, V> + ?Sized> IntoIterator
    for &'a SortedLinearMapInner<K, V, S>
where
    K: Ord,
{
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// An iterator over the items of a [`SortedLinearMap`].
///
/// This struct is created by calling the [`iter`](SortedLinearMap::iter) method on
/// [`SortedLinearMap`].
#[derive(Clone, Debug)]
pub struct Iter<'a, K, V> {
    iter: slice::Iter<'a, (K, V)>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(k, v)| (k, v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|(k, v)| (k, v))
    }
}

impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> {}
impl<'a, K, V> FusedIterator for Iter<'a, K, V> {}

/// An iterator over the items of a [`SortedLinearMap`] that allows modifying the values.
///
/// This struct is created by calling the [`iter_mut`](SortedLinearMap::iter_mut) method on
/// [`SortedLinearMap`].
#[derive(Debug)]
pub struct IterMut<'a, K, V> {
    iter: slice::IterMut<'a, (K, V)>,
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(k, v)| (k as &K, v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for IterMut<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|(k, v)| (k as &K, v))
    }
}

impl<'a, K, V> ExactSizeIterator for IterMut<'a, K, V> {}
impl<'a, K, V> FusedIterator for IterMut<'a, K, V> {}

/// An iterator over a sub-range of a [`SortedLinearMap`]'s entries.
///
/// This struct is created by calling the [`range`](SortedLinearMap::range) method on
/// [`SortedLinearMap`].
#[derive(Clone, Debug)]
pub struct Range<'a, K, V> {
    iter: slice::Iter<'a, (K, V)>,
}

impl<'a, K, V> Iterator for Range<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(k, v)| (k, v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for Range<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|(k, v)| (k, v))
    }
}

impl<'a, K, V> ExactSizeIterator for Range<'a, K, V> {}
impl<'a, K, V> FusedIterator for Range<'a, K, V> {}

/// A mutable iterator over a sub-range of a [`SortedLinearMap`]'s entries.
///
/// This struct is created by calling the [`range_mut`](SortedLinearMap::range_mut) method on
/// [`SortedLinearMap`].
#[derive(Debug)]
pub struct RangeMut<'a, K, V> {
    iter: slice::IterMut<'a, (K, V)>,
}

impl<'a, K, V> Iterator for RangeMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(k, v)| (k as &K, v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, K, V> DoubleEndedIterator for RangeMut<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next_back().map(|(k, v)| (k as &K, v))
    }
}

impl<'a, K, V> ExactSizeIterator for RangeMut<'a, K, V> {}
impl<'a, K, V> FusedIterator for RangeMut<'a, K, V> {}

impl<
        K,
        V1,
        V2,
        S1: SortedLinearMapStorage<K, V1> + ?Sized,
        S2: SortedLinearMapStorage<K, V2> + ?Sized,
    > PartialEq<SortedLinearMapInner<K, V2, S2>> for SortedLinearMapInner<K, V1, S1>
where
    K: Ord,
    V1: PartialEq<V2>,
{
    fn eq(&self, other: &SortedLinearMapInner<K, V2, S2>) -> bool {
        // Both maps are sorted, so pairwise comparison suffices.
        self.len() == other.len()
            && self
                .iter()
                .zip(other.iter())
                .all(|((k1, v1), (k2, v2))| k1.cmp(k2) == Ordering::Equal && *v1 == *v2)
    }
}

impl<K, V, S: SortedLinearMapStorage<K, V> + ?Sized> Eq for SortedLinearMapInner<K, V, S>
where
    K: Ord,
    V: PartialEq,
{
}

impl<
        K,
        V,
        S1: SortedLinearMapStorage<K, V> + ?Sized,
        S2: SortedLinearMapStorage<K, V> + ?Sized,
    > PartialOrd<SortedLinearMapInner<K, V, S2>> for SortedLinearMapInner<K, V, S1>
where
    K: Ord,
    V: PartialOrd,
{
    fn partial_cmp(&self, other: &SortedLinearMapInner<K, V, S2>) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<K, V, S: SortedLinearMapStorage<K, V> + ?Sized> Ord for SortedLinearMapInner<K, V, S>
where
    K: Ord,
    V: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<K, V, S: SortedLinearMapStorage<K, V> + ?Sized> Hash for SortedLinearMapInner<K, V, S>
where
    K: Ord + Hash,
    V: Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        for entry in self.iter() {
            entry.hash(state);
        }
    }
}

/// A view into an entry in the map.
pub enum Entry<'a, K, V> {
    /// The entry corresponding to the key `K` exists in the map.
    Occupied(OccupiedEntry<'a, K, V>),
    /// The entry corresponding to the key `K` does not exist in the map.
    Vacant(VacantEntry<'a, K, V>),
}

/// An occupied entry which can be manipulated.
pub struct OccupiedEntry<'a, K, V> {
    // SAFETY: `idx` must not be modified after construction, and
    // the size of `map` must not be changed.
    idx: usize,
    map: &'a mut SortedLinearMapView<K, V>,
}

impl<'a, K, V> OccupiedEntry<'a, K, V>
where
    K: Ord,
{
    /// Gets a reference to the key that this entry corresponds to.
    pub fn key(&self) -> &K {
        // SAFETY: Valid idx from OccupiedEntry construction
        let (k, _v) = unsafe { self.map.buffer.get_unchecked(self.idx) };
        k
    }

    /// Removes this entry from the map and yields its corresponding key and value.
    pub fn remove_entry(self) -> (K, V) {
        self.map.buffer.remove(self.idx)
    }

    /// Removes this entry from the map and yields its corresponding value.
    pub fn remove(self) -> V {
        self.remove_entry().1
    }

    /// Gets a reference to the value associated with this entry.
    pub fn get(&self) -> &V {
        // SAFETY: Valid idx from OccupiedEntry construction
        let (_k, v) = unsafe { self.map.buffer.get_unchecked(self.idx) };
        v
    }

    /// Gets a mutable reference to the value associated with this entry.
    pub fn get_mut(&mut self) -> &mut V {
        // SAFETY: Valid idx from OccupiedEntry construction
        let (_k, v) = unsafe { self.map.buffer.get_unchecked_mut(self.idx) };
        v
    }

    /// Consumes this entry and yields a reference to the underlying value.
    pub fn into_mut(self) -> &'a mut V {
        // SAFETY: Valid idx from OccupiedEntry construction
        let (_k, v) = unsafe { self.map.buffer.get_unchecked_mut(self.idx) };
        v
    }

    /// Overwrites the underlying map's value with this entry's value, returning the old value.
    pub fn insert(self, value: V) -> V {
        // SAFETY: Valid idx from OccupiedEntry construction
        let (_k, v) = unsafe { self.map.buffer.get_unchecked_mut(self.idx) };
        mem::replace(v, value)
    }
}

/// A view into a vacant slot in the underlying map.
pub struct VacantEntry<'a, K, V> {
    // SAFETY: `idx` must be the position at which `key` should be inserted to keep the map
    // sorted, and the map must not be mutated between construction and `insert`.
    idx: usize,
    key: K,
    map: &'a mut SortedLinearMapView<K, V>,
}

impl<'a, K, V> VacantEntry<'a, K, V>
where
    K: Ord,
{
    /// Get the key associated with this entry.
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Consumes this entry to yield the key associated with it.
    pub fn into_key(self) -> K {
        self.key
    }

    /// Inserts this entry into the underlying map and yields a mutable reference to the inserted
    /// value. If the map is at capacity the value is returned instead.
    pub fn insert(self, value: V) -> Result<&'a mut V, V> {
        self.map
            .buffer
            .insert(self.idx, (self.key, value))
            .map_err(|(_k, v)| v)?;
        let r = &mut self.map.buffer[self.idx];
        Ok(&mut r.1)
    }
}

#[cfg(test)]
mod test {
    use static_assertions::assert_not_impl_any;

    use super::{Entry, SortedLinearMap, SortedLinearMapView};

    // Ensure a `SortedLinearMap` containing `!Send` keys stays `!Send` itself.
    assert_not_impl_any!(SortedLinearMap<*const (), (), 4>: Send);
    // Ensure a `SortedLinearMap` containing `!Send` values stays `!Send` itself.
    assert_not_impl_any!(SortedLinearMap<(), *const (), 4>: Send);

    #[test]
    fn static_new() {
        static mut _L: SortedLinearMap<i32, i32, 8> = SortedLinearMap::new();
    }

    #[test]
    fn sorted_iteration() {
        let mut map: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
        map.insert(3, "c").unwrap();
        map.insert(1, "a").unwrap();
        map.insert(4, "d").unwrap();
        map.insert(2, "b").unwrap();

        let keys: crate::Vec<_, 8> = map.keys().copied().collect();
        assert_eq!(&keys[..], &[1, 2, 3, 4]);
    }

    #[test]
    fn borrow() {
        use crate::String;

        let mut map = SortedLinearMap::<_, _, 8>::new();

        let s = String::<64>::try_from("Hello, world!").unwrap();
        map.insert(s, 42).unwrap();

        assert_eq!(map.get("Hello, world!").unwrap(), &42);
    }

    #[test]
    fn partial_eq() {
        {
            let mut a = SortedLinearMap::<_, _, 1>::new();
            a.insert("k1", "v1").unwrap();

            let mut b = SortedLinearMap::<_, _, 2>::new();
            b.insert("k1", "v1").unwrap();

            assert!(a == b);

            b.insert("k2", "v2").unwrap();

            assert!(a != b);
        }

        {
            let mut a = SortedLinearMap::<_, _, 2>::new();
            a.insert("k1", "v1").unwrap();
            a.insert("k2", "v2").unwrap();

            let mut b = SortedLinearMap::<_, _, 2>::new();
            b.insert("k2", "v2").unwrap();
            b.insert("k1", "v1").unwrap();

            assert!(a == b);
        }
    }

    #[test]
    fn drop() {
        droppable!();

        {
            let mut v: SortedLinearMap<i32, Droppable, 2> = SortedLinearMap::new();
            v.insert(0, Droppable::new()).ok().unwrap();
            v.insert(1, Droppable::new()).ok().unwrap();
            v.remove(&1).unwrap();
        }

        assert_eq!(Droppable::count(), 0);

        {
            let mut v: SortedLinearMap<i32, Droppable, 2> = SortedLinearMap::new();
            v.insert(0, Droppable::new()).ok().unwrap();
            v.insert(1, Droppable::new()).ok().unwrap();
        }

        assert_eq!(Droppable::count(), 0);
    }

    #[test]
    fn into_iter() {
        let mut src: SortedLinearMap<_, _, 4> = SortedLinearMap::new();
        src.insert("k4", "v4").unwrap();
        src.insert("k2", "v2").unwrap();
        src.insert("k1", "v1").unwrap();
        src.insert("k3", "v3").unwrap();
        let collected: crate::Vec<_, 4> = src.clone().into_iter().collect();
        assert_eq!(
            &collected[..],
            &[("k1", "v1"), ("k2", "v2"), ("k3", "v3"), ("k4", "v4")]
        );
    }

    #[test]
    fn into_iter_len() {
        let mut src: SortedLinearMap<_, _, 2> = SortedLinearMap::new();
        src.insert("k1", "v1").unwrap();
        src.insert("k2", "v2").unwrap();
        let mut items = src.into_iter();
        assert_eq!(items.len(), 2);
        let _ = items.next();
        assert_eq!(items.len(), 1);
        let _ = items.next();
        assert_eq!(items.len(), 0);
    }

    fn _test_variance_value<'a: 'b, 'b>(
        x: SortedLinearMap<u32, &'a (), 42>,
    ) -> SortedLinearMap<u32, &'b (), 42> {
        x
    }
    fn _test_variance_value_view<'a: 'b, 'b, 'c>(
        x: &'c SortedLinearMapView<u32, &'a ()>,
    ) -> &'c SortedLinearMapView<u32, &'b ()> {
        x
    }
    fn _test_variance_key<'a: 'b, 'b>(
        x: SortedLinearMap<&'a (), u32, 42>,
    ) -> SortedLinearMap<&'b (), u32, 42> {
        x
    }
    fn _test_variance_key_view<'a: 'b, 'b, 'c>(
        x: &'c SortedLinearMapView<&'a (), u32>,
    ) -> &'c SortedLinearMapView<&'b (), u32> {
        x
    }

    #[test]
    fn partial_eq_floats() {
        // Make sure `PartialEq` is implemented even if `V` doesn't implement `Eq`.
        let map: SortedLinearMap<usize, f32, 4> = Default::default();
        assert_eq!(map, map);
    }

    #[test]
    #[cfg(feature = "zeroize")]
    fn test_sorted_linear_map_zeroize() {
        use zeroize::Zeroize;

        let mut map: SortedLinearMap<u8, u8, 8> = SortedLinearMap::new();
        for i in 1..=8 {
            map.insert(i, i * 10).unwrap();
        }

        assert_eq!(map.len(), 8);
        assert_eq!(map.get(&5), Some(&50));

        // zeroized using Vec's implementation
        map.zeroize();

        assert_eq!(map.len(), 0);
        assert!(map.is_empty());
    }

    // tests that use this constant take too long to run under miri, specially on CI, with a map of
    // this size so make the map smaller when using miri
    #[cfg(not(miri))]
    const MAP_SLOTS: usize = 4096;
    #[cfg(miri)]
    const MAP_SLOTS: usize = 64;
    fn almost_filled_map() -> SortedLinearMap<usize, usize, MAP_SLOTS> {
        let mut almost_filled = SortedLinearMap::new();
        for i in 1..MAP_SLOTS {
            almost_filled.insert(i, i).unwrap();
        }
        almost_filled
    }

    #[test]
    fn remove() {
        let mut src = almost_filled_map();
        // key doesn't exist
        let k = 0;
        let r = src.remove(&k);
        assert!(r.is_none());

        let k = 5;
        let v = 5;
        let r = src.remove(&k);
        assert_eq!(r, Some(v));
        let r = src.remove(&k);
        assert!(r.is_none());
        assert_eq!(src.len(), MAP_SLOTS - 2);
    }

    #[test]
    fn replace() {
        let mut src = almost_filled_map();
        src.insert(10, 1000).unwrap();
        let v = src.get(&10).unwrap();
        assert_eq!(*v, 1000);

        let mut src = almost_filled_map();
        let v = src.get_mut(&10).unwrap();
        *v = 500;
        let v = src.get(&10).unwrap();
        assert_eq!(*v, 500);
    }

    #[test]
    fn retain() {
        let mut src = almost_filled_map();
        src.retain(|k, _v| k % 2 == 0);
        src.retain(|k, _v| k % 3 == 0);

        for (k, v) in src.iter() {
            assert_eq!(k, v);
            assert_eq!(k % 2, 0);
            assert_eq!(k % 3, 0);
        }

        let mut src = almost_filled_map();
        src.retain(|_k, _v| false);
        assert!(src.is_empty());

        let mut src = almost_filled_map();
        src.retain(|_k, _v| true);
        assert_eq!(src.len(), MAP_SLOTS - 1);
        src.insert(0, 0).unwrap();
        src.retain(|_k, _v| true);
        assert_eq!(src.len(), MAP_SLOTS);
    }

    #[test]
    fn entry_find() {
        let key = 0;
        let value = 0;
        let mut src = almost_filled_map();
        let entry = src.entry(key);
        match entry {
            Entry::Occupied(_) => {
                panic!("Found entry without inserting");
            }
            Entry::Vacant(v) => {
                assert_eq!(&key, v.key());
                assert_eq!(key, v.into_key());
            }
        }
        src.insert(key, value).unwrap();
        let entry = src.entry(key);
        match entry {
            Entry::Occupied(mut o) => {
                assert_eq!(&key, o.key());
                assert_eq!(&value, o.get());
                assert_eq!(&value, o.get_mut());
                assert_eq!(&value, o.into_mut());
            }
            Entry::Vacant(_) => {
                panic!("Entry not found");
            }
        }
    }

    #[test]
    fn entry_vacant_insert() {
        let key = 0;
        let value = 0;
        let mut src = almost_filled_map();
        assert_eq!(MAP_SLOTS - 1, src.len());
        let entry = src.entry(key);
        match entry {
            Entry::Occupied(_) => {
                panic!("Entry found when empty");
            }
            Entry::Vacant(v) => {
                assert_eq!(value, *v.insert(value).unwrap());
            }
        };
        assert_eq!(value, *src.get(&key).unwrap());
    }

    #[test]
    fn entry_vacant_full_insert() {
        let mut src = almost_filled_map();

        // fill the map
        let key = MAP_SLOTS * 2;
        let value = key;
        src.insert(key, value).unwrap();
        assert_eq!(MAP_SLOTS, src.len());

        let key = 0;
        let value = 0;
        let entry = src.entry(key);
        match entry {
            Entry::Occupied(_) => {
                panic!("Entry found when missing");
            }
            Entry::Vacant(v) => {
                // Value is returned since the map is full
                assert_eq!(value, v.insert(value).unwrap_err());
            }
        };
        assert!(src.get(&key).is_none());
    }

    #[test]
    fn entry_occupied_insert() {
        let key = 0;
        let value = 0;
        let value2 = 5;
        let mut src = almost_filled_map();
        assert_eq!(MAP_SLOTS - 1, src.len());
        src.insert(key, value).unwrap();
        let entry = src.entry(key);
        match entry {
            Entry::Occupied(o) => {
                assert_eq!(value, o.insert(value2));
            }
            Entry::Vacant(_) => {
                panic!("Entry not found");
            }
        };
        assert_eq!(value2, *src.get(&key).unwrap());
    }

    #[test]
    fn entry_remove_entry() {
        let key = 0;
        let value = 0;
        let mut src = almost_filled_map();
        src.insert(key, value).unwrap();
        assert_eq!(MAP_SLOTS, src.len());
        let entry = src.entry(key);
        match entry {
            Entry::Occupied(o) => {
                assert_eq!((key, value), o.remove_entry());
            }
            Entry::Vacant(_) => {
                panic!("Entry not found")
            }
        };
        assert_eq!(MAP_SLOTS - 1, src.len());
        assert!(!src.contains_key(&key));
    }

    #[test]
    fn entry_remove() {
        let key = 0;
        let value = 0;
        let mut src = almost_filled_map();
        src.insert(key, value).unwrap();
        assert_eq!(MAP_SLOTS, src.len());
        let entry = src.entry(key);
        match entry {
            Entry::Occupied(o) => {
                assert_eq!(value, o.remove());
            }
            Entry::Vacant(_) => {
                panic!("Entry not found");
            }
        };
        assert_eq!(MAP_SLOTS - 1, src.len());
    }

    #[test]
    fn first_last_pop() {
        let mut map: SortedLinearMap<_, _, 4> = SortedLinearMap::new();
        assert_eq!(map.first_key_value(), None);
        assert_eq!(map.last_key_value(), None);
        assert_eq!(map.pop_first(), None);
        assert_eq!(map.pop_last(), None);

        map.insert(3, "c").unwrap();
        map.insert(1, "a").unwrap();
        map.insert(2, "b").unwrap();
        assert_eq!(map.first_key_value(), Some((&1, &"a")));
        assert_eq!(map.last_key_value(), Some((&3, &"c")));

        assert_eq!(map.pop_first(), Some((1, "a")));
        assert_eq!(map.pop_last(), Some((3, "c")));
        assert_eq!(map.pop_first(), Some((2, "b")));
        assert_eq!(map.pop_first(), None);
    }

    #[test]
    fn range() {
        let mut map: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
        for k in [1, 3, 5, 7, 9] {
            map.insert(k, k * 10).unwrap();
        }

        let collect = |iter: super::Range<'_, i32, i32>| -> crate::Vec<(i32, i32), 8> {
            iter.map(|(k, v)| (*k, *v)).collect()
        };

        assert_eq!(
            &collect(map.range(..))[..],
            &[(1, 10), (3, 30), (5, 50), (7, 70), (9, 90)]
        );
        assert_eq!(&collect(map.range(3..7))[..], &[(3, 30), (5, 50)]);
        assert_eq!(&collect(map.range(3..=7))[..], &[(3, 30), (5, 50), (7, 70)]);
        assert_eq!(&collect(map.range(..5))[..], &[(1, 10), (3, 30)]);
        assert_eq!(&collect(map.range(5..))[..], &[(5, 50), (7, 70), (9, 90)]);
        // keys not in the map still bound correctly
        assert_eq!(&collect(map.range(2..8))[..], &[(3, 30), (5, 50), (7, 70)]);
        // excluded start
        let r: crate::Vec<(i32, i32), 8> = map
            .range((core::ops::Bound::Excluded(3), core::ops::Bound::Included(7)))
            .map(|(k, v)| (*k, *v))
            .collect();
        assert_eq!(&r[..], &[(5, 50), (7, 70)]);
    }

    #[test]
    fn range_mut() {
        let mut map: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
        for k in [1, 3, 5, 7, 9] {
            map.insert(k, 0).unwrap();
        }
        for (_, v) in map.range_mut(3..8) {
            *v = 1;
        }
        assert_eq!(map.get(&1), Some(&0));
        assert_eq!(map.get(&3), Some(&1));
        assert_eq!(map.get(&5), Some(&1));
        assert_eq!(map.get(&7), Some(&1));
        assert_eq!(map.get(&9), Some(&0));
    }

    #[test]
    fn remove_entry() {
        let mut map: SortedLinearMap<_, _, 4> = SortedLinearMap::new();
        map.insert(1, "a").unwrap();
        map.insert(2, "b").unwrap();
        assert_eq!(map.remove_entry(&1), Some((1, "a")));
        assert_eq!(map.remove_entry(&1), None);
        assert_eq!(map.len(), 1);
    }

    #[test]
    fn ordering() {
        let mut a: SortedLinearMap<_, _, 4> = SortedLinearMap::new();
        a.insert(1, "a").unwrap();
        a.insert(2, "b").unwrap();

        let mut b: SortedLinearMap<_, _, 4> = SortedLinearMap::new();
        b.insert(1, "a").unwrap();
        b.insert(2, "c").unwrap();

        assert!(a < b);
        assert!(a.cmp(&b) == core::cmp::Ordering::Less);
    }

    #[test]
    fn hash_matches_eq() {
        use core::hash::{Hash, Hasher};
        use hash32::FnvHasher;

        let mut a: SortedLinearMap<_, _, 4> = SortedLinearMap::new();
        a.insert(2, "b").unwrap();
        a.insert(1, "a").unwrap();

        let mut b: SortedLinearMap<_, _, 8> = SortedLinearMap::new();
        b.insert(1, "a").unwrap();
        b.insert(2, "b").unwrap();

        fn hash<T: Hash>(v: &T) -> u64 {
            let mut h = FnvHasher::default();
            v.hash(&mut h);
            h.finish()
        }

        assert_eq!(a, b);
        assert_eq!(hash(&a), hash(&b));
    }

    #[test]
    #[should_panic]
    fn range_start_after_end_panics() {
        let mut map: SortedLinearMap<i32, i32, 4> = SortedLinearMap::new();
        map.insert(1, 1).unwrap();
        #[allow(clippy::reversed_empty_ranges)]
        let _ = map.range(5..3);
    }

    #[test]
    #[should_panic]
    fn range_excluded_equal_panics() {
        let mut map: SortedLinearMap<i32, i32, 4> = SortedLinearMap::new();
        map.insert(1, 1).unwrap();
        let _ = map.range((core::ops::Bound::Excluded(3), core::ops::Bound::Excluded(3)));
    }
}

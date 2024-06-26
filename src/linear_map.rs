use core::{borrow::Borrow, fmt, mem, ops, slice};

use crate::{Vec, VecView};

mod sealed {
    /// <div class="warn">This is private API and should not be used</div>
    pub struct LinearMapInner<V: ?Sized> {
        pub(super) buffer: V,
    }
}

// Workaround https://github.com/rust-lang/rust/issues/119015. This is required so that the methods on `VecView` and `Vec` are properly documented.
// cfg(doc) prevents `LinearMapInner` being part of the public API.
// doc(hidden) prevents the `pub use sealed::StringInner` from being visible in the documentation.
#[cfg(doc)]
#[doc(hidden)]
pub use sealed::LinearMapInner as _;

/// A fixed capacity map/dictionary that performs lookups via linear search.
///
/// Note that as this map doesn't use hashing so most operations are *O*(n) instead of *O*(1).
pub type LinearMap<K, V, const N: usize> = sealed::LinearMapInner<Vec<(K, V), N>>;

/// A [`LinearMap`] with dynamic capacity
///
/// [`LinearMap`] coerces to `LinearMapView`. `LinearMapView` is `!Sized`, meaning it can only ever be used by reference
///
/// Unlike [`LinearMap`], `LinearMapView` does not have an `N` const-generic parameter.
/// This has the ergonomic advantage of making it possible to use functions without needing to know at
/// compile-time the size of the buffers used, for example for use in `dyn` traits.
///
/// `LinearMapView` is to `LinearMap` what [`VecView`] is to [`Vec`].
///
/// ```rust
/// use heapless::{LinearMap, LinearMapView};
///
/// let mut map: LinearMap<_, _, 8> = LinearMap::new();
/// let map_view: &mut LinearMapView<_, _> = &mut map;
/// map_view.insert(1, "a").unwrap();
/// if let Some(x) = map_view.get_mut(&1) {
///     *x = "b";
/// }
/// assert_eq!(map_view[&1], "b");
/// ```
pub type LinearMapView<K, V> = sealed::LinearMapInner<VecView<(K, V)>>;

impl<K, V, const N: usize> LinearMap<K, V, N> {
    /// Creates an empty `LinearMap`.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::{LinearMap, LinearMapView};
    ///
    /// // allocate the map on the stack
    /// let mut map: LinearMap<&str, isize, 8> = LinearMap::new();
    ///
    /// // allocate the map in a static variable
    /// static mut MAP: LinearMap<&str, isize, 8> = LinearMap::new();
    ///
    /// // allocate the map in a static variable, erasing the const generic
    /// static mut MAP_VIEW: &mut LinearMapView<&str, isize> = &mut LinearMap::<_, _, 8>::new();
    /// ```
    pub const fn new() -> Self {
        Self { buffer: Vec::new() }
    }
}

impl<K, V, const N: usize> LinearMap<K, V, N>
where
    K: Eq,
{
    /// Get a reference to the `LinearMap`, erasing the `N` const-generic.
    ///
    /// ```rust
    /// use heapless::{LinearMap, LinearMapView};
    ///
    /// let mut map: LinearMap<_, _, 8> = LinearMap::new();
    /// map.insert(1, "a").unwrap();
    /// if let Some(x) = map.get_mut(&1) {
    ///     *x = "b";
    /// }
    /// let map_view: &LinearMapView<_, _> = map.as_view();
    /// assert_eq!(map_view[&1], "b");
    /// ```
    ///
    /// It is often preferable to do the same through type coerction, since `LinearMap<K, V, N>` implements `Unsize<LinearMapView<K, V>>`:
    ///
    /// ```rust
    /// # use heapless::{LinearMap, LinearMapView};
    ///
    /// let map: LinearMap<&str, &str, 8> = LinearMap::new();
    /// let map_view: &LinearMapView<_, _> = &map;
    /// ```
    pub fn as_view(&self) -> &LinearMapView<K, V> {
        self
    }

    /// Get a mutable reference to the `LinearMap`, erasing the `N` const-generic.
    ///
    /// ```rust
    /// use heapless::{LinearMap, LinearMapView};
    ///
    /// let mut map: LinearMap<_, _, 8> = LinearMap::new();
    /// let map_view: &mut LinearMapView<_, _> = map.as_mut_view();
    /// map_view.insert(1, "a").unwrap();
    /// if let Some(x) = map_view.get_mut(&1) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map_view[&1], "b");
    /// ```
    ///
    /// It is often preferable to do the same through type coerction, since `LinearMap<K, V, N>` implements `Unsize<LinearMapView<K, V>>`:
    ///
    /// ```rust
    /// # use heapless::{LinearMap, LinearMapView};
    ///
    /// let mut map: LinearMap<&str, &str, 8> = LinearMap::new();
    /// let map_view: &mut LinearMapView<_, _> = &mut map;
    /// ```
    pub fn as_mut_view(&mut self) -> &mut LinearMapView<K, V> {
        self
    }

    /// Returns the number of elements that the map can hold.
    ///
    /// Computes in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    ///
    /// let map: LinearMap<&str, isize, 8> = LinearMap::new();
    /// assert_eq!(map.capacity(), 8);
    /// ```
    pub fn capacity(&self) -> usize {
        N
    }

    /// Clears the map, removing all key-value pairs.
    ///
    /// Computes in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    ///
    /// let mut map: LinearMap<_, _, 8> = LinearMap::new();
    /// map.insert(1, "a").unwrap();
    /// map.clear();
    /// assert!(map.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.as_mut_view().clear()
    }

    /// Returns true if the map contains a value for the specified key.
    ///
    /// Computes in *O*(n) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    ///
    /// let mut map: LinearMap<_, _, 8> = LinearMap::new();
    /// map.insert(1, "a").unwrap();
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    pub fn contains_key(&self, key: &K) -> bool {
        self.as_view().contains_key(key)
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// Computes in *O*(n) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    ///
    /// let mut map: LinearMap<_, _, 8> = LinearMap::new();
    /// map.insert(1, "a").unwrap();
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.as_view().get(key)
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// Computes in *O*(n) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    ///
    /// let mut map: LinearMap<_, _, 8> = LinearMap::new();
    /// map.insert(1, "a").unwrap();
    /// if let Some(x) = map.get_mut(&1) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map[&1], "b");
    /// ```
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.as_mut_view().get_mut(key)
    }

    /// Returns the number of elements in this map.
    ///
    /// Computes in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    ///
    /// let mut a: LinearMap<_, _, 8> = LinearMap::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(1, "a").unwrap();
    /// assert_eq!(a.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.as_view().len()
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old value is returned.
    ///
    /// Computes in *O*(n) time
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    ///
    /// let mut map: LinearMap<_, _, 8> = LinearMap::new();
    /// assert_eq!(map.insert(37, "a").unwrap(), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(37, "b").unwrap();
    /// assert_eq!(map.insert(37, "c").unwrap(), Some("b"));
    /// assert_eq!(map[&37], "c");
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Result<Option<V>, (K, V)> {
        self.as_mut_view().insert(key, value)
    }

    /// Returns true if the map contains no elements.
    ///
    /// Computes in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    ///
    /// let mut a: LinearMap<_, _, 8> = LinearMap::new();
    /// assert!(a.is_empty());
    /// a.insert(1, "a").unwrap();
    /// assert!(!a.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.as_view().is_empty()
    }

    /// An iterator visiting all key-value pairs in arbitrary order.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    ///
    /// let mut map: LinearMap<_, _, 8> = LinearMap::new();
    /// map.insert("a", 1).unwrap();
    /// map.insert("b", 2).unwrap();
    /// map.insert("c", 3).unwrap();
    ///
    /// for (key, val) in map.iter() {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, K, V> {
        self.as_view().iter()
    }

    /// An iterator visiting all key-value pairs in arbitrary order,
    /// with mutable references to the values.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    ///
    /// let mut map: LinearMap<_, _, 8> = LinearMap::new();
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
        self.as_mut_view().iter_mut()
    }

    /// An iterator visiting all keys in arbitrary order.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    ///
    /// let mut map: LinearMap<_, _, 8> = LinearMap::new();
    /// map.insert("a", 1).unwrap();
    /// map.insert("b", 2).unwrap();
    /// map.insert("c", 3).unwrap();
    ///
    /// for key in map.keys() {
    ///     println!("{}", key);
    /// }
    /// ```
    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.as_view().keys()
    }

    /// Removes a key from the map, returning the value at
    /// the key if the key was previously in the map.
    ///
    /// Computes in *O*(n) time
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    ///
    /// let mut map: LinearMap<_, _, 8> = LinearMap::new();
    /// map.insert(1, "a").unwrap();
    /// assert_eq!(map.remove(&1), Some("a"));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.as_mut_view().remove(key)
    }

    /// An iterator visiting all values in arbitrary order.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    ///
    /// let mut map: LinearMap<_, _, 8> = LinearMap::new();
    /// map.insert("a", 1).unwrap();
    /// map.insert("b", 2).unwrap();
    /// map.insert("c", 3).unwrap();
    ///
    /// for val in map.values() {
    ///     println!("{}", val);
    /// }
    /// ```
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.as_view().values()
    }

    /// An iterator visiting all values mutably in arbitrary order.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    ///
    /// let mut map: LinearMap<_, _, 8> = LinearMap::new();
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
        self.as_mut_view().values_mut()
    }
}

impl<'a, K, V, Q, const N: usize> ops::Index<&'a Q> for LinearMap<K, V, N>
where
    K: Borrow<Q> + Eq,
    Q: Eq + ?Sized,
{
    type Output = V;

    fn index(&self, key: &Q) -> &V {
        self.as_view().index(key)
    }
}

impl<'a, K, V, Q, const N: usize> ops::IndexMut<&'a Q> for LinearMap<K, V, N>
where
    K: Borrow<Q> + Eq,
    Q: Eq + ?Sized,
{
    fn index_mut(&mut self, key: &Q) -> &mut V {
        self.as_mut_view().index_mut(key)
    }
}

impl<K, V, const N: usize> Default for LinearMap<K, V, N>
where
    K: Eq,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V, const N: usize> Clone for LinearMap<K, V, N>
where
    K: Eq + Clone,
    V: Clone,
{
    fn clone(&self) -> Self {
        Self {
            buffer: self.buffer.clone(),
        }
    }
}

impl<K, V, const N: usize> fmt::Debug for LinearMap<K, V, N>
where
    K: Eq + fmt::Debug,
    V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_view().fmt(f)
    }
}

impl<K, V> LinearMapView<K, V>
where
    K: Eq,
{
    /// Returns the number of elements that the map can hold.
    ///
    /// Computes in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::{LinearMap, LinearMapView};
    ///
    /// let map: LinearMap<&str, isize, 8> = LinearMap::new();
    /// let map_view: &LinearMapView<&str, isize> = &map;
    /// assert_eq!(map_view.capacity(), 8);
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
    /// use heapless::{LinearMap, LinearMapView};
    ///
    /// let mut map: LinearMap<_, _, 8> = LinearMap::new();
    /// let map_view: &mut LinearMapView<_, _> = &mut map;
    /// map_view.insert(1, "a").unwrap();
    /// map_view.clear();
    /// assert!(map_view.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.buffer.clear()
    }

    /// Returns true if the map contains a value for the specified key.
    ///
    /// Computes in *O*(n) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::{LinearMap, LinearMapView};
    ///
    /// let mut map: LinearMap<_, _, 8> = LinearMap::new();
    /// let map_view: &mut LinearMapView<_, _> = &mut map;
    /// map_view.insert(1, "a").unwrap();
    /// assert_eq!(map_view.contains_key(&1), true);
    /// assert_eq!(map_view.contains_key(&2), false);
    /// ```
    pub fn contains_key(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// Computes in *O*(n) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::{LinearMap, LinearMapView};
    ///
    /// let mut map: LinearMap<_, _, 8> = LinearMap::new();
    /// let map_view: &mut LinearMapView<_, _> = &mut map;
    /// map_view.insert(1, "a").unwrap();
    /// assert_eq!(map_view.get(&1), Some(&"a"));
    /// assert_eq!(map_view.get(&2), None);
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.iter()
            .find(|&(k, _)| k.borrow() == key)
            .map(|(_, v)| v)
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// Computes in *O*(n) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::{LinearMap, LinearMapView};
    ///
    /// let mut map: LinearMap<_, _, 8> = LinearMap::new();
    /// let map_view: &mut LinearMapView<_, _> = &mut map;
    /// map_view.insert(1, "a").unwrap();
    /// if let Some(x) = map_view.get_mut(&1) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map_view[&1], "b");
    /// ```
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.iter_mut()
            .find(|&(k, _)| k.borrow() == key)
            .map(|(_, v)| v)
    }

    /// Returns the number of elements in this map.
    ///
    /// Computes in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::{LinearMap, LinearMapView};
    ///
    /// let mut a: LinearMap<_, _, 8> = LinearMap::new();
    /// let mut a_view: &mut LinearMapView<_, _> = &mut a;
    /// assert_eq!(a_view.len(), 0);
    /// a_view.insert(1, "a").unwrap();
    /// assert_eq!(a_view.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.buffer.len()
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old value is returned.
    ///
    /// Computes in *O*(n) time
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::{LinearMap, LinearMapView};
    ///
    /// let mut map: LinearMap<_, _, 8> = LinearMap::new();
    /// let map_view: &mut LinearMapView<_, _> = &mut map;
    /// assert_eq!(map_view.insert(37, "a").unwrap(), None);
    /// assert_eq!(map_view.is_empty(), false);
    ///
    /// map_view.insert(37, "b").unwrap();
    /// assert_eq!(map_view.insert(37, "c").unwrap(), Some("b"));
    /// assert_eq!(map_view[&37], "c");
    /// ```
    pub fn insert(&mut self, key: K, mut value: V) -> Result<Option<V>, (K, V)> {
        if let Some((_, v)) = self.iter_mut().find(|&(k, _)| *k == key) {
            mem::swap(v, &mut value);
            return Ok(Some(value));
        }

        self.buffer.push((key, value))?;
        Ok(None)
    }

    /// Returns true if the map contains no elements.
    ///
    /// Computes in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::{LinearMap, LinearMapView};
    ///
    /// let mut a: LinearMap<_, _, 8> = LinearMap::new();
    /// let a_view: &mut LinearMapView<_, _> = &mut a;
    /// assert!(a_view.is_empty());
    /// a_view.insert(1, "a").unwrap();
    /// assert!(!a_view.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// An iterator visiting all key-value pairs in arbitrary order.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::{LinearMap, LinearMapView};
    ///
    /// let mut map: LinearMap<_, _, 8> = LinearMap::new();
    /// let map_view: &mut LinearMapView<_, _> = &mut map;
    /// map_view.insert("a", 1).unwrap();
    /// map_view.insert("b", 2).unwrap();
    /// map_view.insert("c", 3).unwrap();
    ///
    /// for (key, val) in map_view.iter() {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            iter: self.buffer.as_slice().iter(),
        }
    }

    /// An iterator visiting all key-value pairs in arbitrary order,
    /// with mutable references to the values.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::{LinearMap, LinearMapView};
    ///
    /// let mut map: LinearMap<_, _, 8> = LinearMap::new();
    /// let map_view: &mut LinearMapView<_, _> = &mut map;
    /// map_view.insert("a", 1).unwrap();
    /// map_view.insert("b", 2).unwrap();
    /// map_view.insert("c", 3).unwrap();
    ///
    /// // Update all values
    /// for (_, val) in map_view.iter_mut() {
    ///     *val = 2;
    /// }
    ///
    /// for (key, val) in &*map_view {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut {
            iter: self.buffer.as_mut_slice().iter_mut(),
        }
    }

    /// An iterator visiting all keys in arbitrary order.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::{LinearMap, LinearMapView};
    ///
    /// let mut map: LinearMap<_, _, 8> = LinearMap::new();
    /// let map_view: &mut LinearMapView<_, _> = &mut map;
    /// map_view.insert("a", 1).unwrap();
    /// map_view.insert("b", 2).unwrap();
    /// map_view.insert("c", 3).unwrap();
    ///
    /// for key in map_view.keys() {
    ///     println!("{}", key);
    /// }
    /// ```
    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.iter().map(|(k, _)| k)
    }

    /// Removes a key from the map, returning the value at
    /// the key if the key was previously in the map.
    ///
    /// Computes in *O*(n) time
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::{LinearMap, LinearMapView};
    ///
    /// let mut map: LinearMap<_, _, 8> = LinearMap::new();
    /// let map_view: &mut LinearMapView<_, _> = &mut map;
    /// map_view.insert(1, "a").unwrap();
    /// assert_eq!(map_view.remove(&1), Some("a"));
    /// assert_eq!(map_view.remove(&1), None);
    /// ```
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        let idx = self
            .keys()
            .enumerate()
            .find(|&(_, k)| k.borrow() == key)
            .map(|(idx, _)| idx);

        idx.map(|idx| self.buffer.swap_remove(idx).1)
    }

    /// An iterator visiting all values in arbitrary order.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::{LinearMap, LinearMapView};
    ///
    /// let mut map: LinearMap<_, _, 8> = LinearMap::new();
    /// let map_view: &mut LinearMapView<_, _> = &mut map;
    /// map_view.insert("a", 1).unwrap();
    /// map_view.insert("b", 2).unwrap();
    /// map_view.insert("c", 3).unwrap();
    ///
    /// for val in map_view.values() {
    ///     println!("{}", val);
    /// }
    /// ```
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.iter().map(|(_, v)| v)
    }

    /// An iterator visiting all values mutably in arbitrary order.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::{LinearMap, LinearMapView};
    ///
    /// let mut map: LinearMap<_, _, 8> = LinearMap::new();
    /// let map_view: &mut LinearMapView<_, _> = &mut map;
    /// map_view.insert("a", 1).unwrap();
    /// map_view.insert("b", 2).unwrap();
    /// map_view.insert("c", 3).unwrap();
    ///
    /// for val in map_view.values_mut() {
    ///     *val += 10;
    /// }
    ///
    /// for val in map_view.values() {
    ///     println!("{}", val);
    /// }
    /// ```
    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut V> {
        self.iter_mut().map(|(_, v)| v)
    }
}

impl<'a, K, V, Q> ops::Index<&'a Q> for LinearMapView<K, V>
where
    K: Borrow<Q> + Eq,
    Q: Eq + ?Sized,
{
    type Output = V;

    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("no entry found for key")
    }
}

impl<'a, K, V, Q> ops::IndexMut<&'a Q> for LinearMapView<K, V>
where
    K: Borrow<Q> + Eq,
    Q: Eq + ?Sized,
{
    fn index_mut(&mut self, key: &Q) -> &mut V {
        self.get_mut(key).expect("no entry found for key")
    }
}

impl<K, V> fmt::Debug for LinearMapView<K, V>
where
    K: Eq + fmt::Debug,
    V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, V, const N: usize> FromIterator<(K, V)> for LinearMap<K, V, N>
where
    K: Eq,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (K, V)>,
    {
        let mut out = Self::new();
        out.buffer.extend(iter);
        out
    }
}

pub struct IntoIter<K, V, const N: usize>
where
    K: Eq,
{
    inner: <Vec<(K, V), N> as IntoIterator>::IntoIter,
}

impl<K, V, const N: usize> Iterator for IntoIter<K, V, N>
where
    K: Eq,
{
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<K, V, const N: usize> IntoIterator for LinearMap<K, V, N>
where
    K: Eq,
{
    type Item = (K, V);
    type IntoIter = IntoIter<K, V, N>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.buffer.into_iter(),
        }
    }
}

impl<'a, K, V, const N: usize> IntoIterator for &'a LinearMap<K, V, N>
where
    K: Eq,
{
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_view().iter()
    }
}

impl<'a, K, V> IntoIterator for &'a LinearMapView<K, V>
where
    K: Eq,
{
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[derive(Clone, Debug)]
pub struct Iter<'a, K, V> {
    iter: slice::Iter<'a, (K, V)>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        // False positive from clippy
        // Option<&(K, V)> -> Option<(&K, &V)>
        #[allow(clippy::map_identity)]
        self.iter.next().map(|(k, v)| (k, v))
    }
}

#[derive(Debug)]
pub struct IterMut<'a, K, V> {
    iter: slice::IterMut<'a, (K, V)>,
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(k, v)| (k as &K, v))
    }
}

impl<K, V, const N: usize, const N2: usize> PartialEq<LinearMap<K, V, N2>> for LinearMap<K, V, N>
where
    K: Eq,
    V: PartialEq,
{
    fn eq(&self, other: &LinearMap<K, V, N2>) -> bool {
        self.len() == other.len()
            && self
                .iter()
                .all(|(key, value)| other.get(key).map_or(false, |v| *value == *v))
    }
}

impl<K, V, const N: usize> Eq for LinearMap<K, V, N>
where
    K: Eq,
    V: PartialEq,
{
}

impl<K, V> PartialEq<LinearMapView<K, V>> for LinearMapView<K, V>
where
    K: Eq,
    V: PartialEq,
{
    fn eq(&self, other: &LinearMapView<K, V>) -> bool {
        self.len() == other.len()
            && self
                .iter()
                .all(|(key, value)| other.get(key).map_or(false, |v| *value == *v))
    }
}

impl<K, V, const N: usize> PartialEq<LinearMap<K, V, N>> for LinearMapView<K, V>
where
    K: Eq,
    V: PartialEq,
{
    fn eq(&self, other: &LinearMap<K, V, N>) -> bool {
        self.eq(other.as_view())
    }
}

impl<K, V, const N: usize> PartialEq<LinearMapView<K, V>> for LinearMap<K, V, N>
where
    K: Eq,
    V: PartialEq,
{
    fn eq(&self, other: &LinearMapView<K, V>) -> bool {
        self.as_view().eq(other)
    }
}

impl<K, V> Eq for LinearMapView<K, V>
where
    K: Eq,
    V: PartialEq,
{
}

#[cfg(test)]
mod test {
    use static_assertions::assert_not_impl_any;

    use super::LinearMap;

    // Ensure a `LinearMap` containing `!Send` keys stays `!Send` itself.
    assert_not_impl_any!(LinearMap<*const (), (), 4>: Send);
    // Ensure a `LinearMap` containing `!Send` values stays `!Send` itself.
    assert_not_impl_any!(LinearMap<(), *const (), 4>: Send);

    #[test]
    fn static_new() {
        static mut _L: LinearMap<i32, i32, 8> = LinearMap::new();
    }

    #[test]
    fn partial_eq() {
        {
            let mut a = LinearMap::<_, _, 1>::new();
            a.insert("k1", "v1").unwrap();

            let mut b = LinearMap::<_, _, 2>::new();
            b.insert("k1", "v1").unwrap();

            assert!(a == b);

            b.insert("k2", "v2").unwrap();

            assert!(a != b);
        }

        {
            let mut a = LinearMap::<_, _, 2>::new();
            a.insert("k1", "v1").unwrap();
            a.insert("k2", "v2").unwrap();

            let mut b = LinearMap::<_, _, 2>::new();
            b.insert("k2", "v2").unwrap();
            b.insert("k1", "v1").unwrap();

            assert!(a == b);
        }
    }

    #[test]
    fn drop() {
        droppable!();

        {
            let mut v: LinearMap<i32, Droppable, 2> = LinearMap::new();
            v.insert(0, Droppable::new()).ok().unwrap();
            v.insert(1, Droppable::new()).ok().unwrap();
            v.remove(&1).unwrap();
        }

        assert_eq!(Droppable::count(), 0);

        {
            let mut v: LinearMap<i32, Droppable, 2> = LinearMap::new();
            v.insert(0, Droppable::new()).ok().unwrap();
            v.insert(1, Droppable::new()).ok().unwrap();
        }

        assert_eq!(Droppable::count(), 0);
    }

    #[test]
    fn into_iter() {
        let mut src: LinearMap<_, _, 4> = LinearMap::new();
        src.insert("k1", "v1").unwrap();
        src.insert("k2", "v2").unwrap();
        src.insert("k3", "v3").unwrap();
        src.insert("k4", "v4").unwrap();
        let clone = src.clone();
        for (k, v) in clone.into_iter() {
            assert_eq!(v, src.remove(k).unwrap());
        }
    }
}

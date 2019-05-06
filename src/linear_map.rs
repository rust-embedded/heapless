use core::{borrow::Borrow, fmt, iter::FromIterator, mem, ops, ptr, slice};

use generic_array::{ArrayLength, GenericArray};

use crate::Vec;

/// A fixed capacity map / dictionary that performs lookups via linear search
///
/// Note that as this map doesn't use hashing so most operations are **O(N)** instead of O(1)
pub struct LinearMap<K, V, N>(#[doc(hidden)] pub crate::i::LinearMap<GenericArray<(K, V), N>>)
where
    N: ArrayLength<(K, V)>,
    K: Eq;

impl<A> crate::i::LinearMap<A> {
    /// `LinearMap` `const` constructor; wrap the returned value in
    /// [`LinearMap`](../struct.LinearMap.html)
    pub const fn new() -> Self {
        Self {
            buffer: crate::i::Vec::new(),
        }
    }
}

impl<K, V, N> LinearMap<K, V, N>
where
    N: ArrayLength<(K, V)>,
    K: Eq,
{
    /// Creates an empty `LinearMap`
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    /// use heapless::consts::*;
    ///
    /// // allocate the map on the stack
    /// let mut map: LinearMap<&str, isize, U8> = LinearMap::new();
    ///
    /// // allocate the map in a static variable
    /// static mut MAP: LinearMap<&str, isize, U8> = LinearMap(heapless::i::LinearMap::new());
    /// ```
    pub fn new() -> Self {
        LinearMap(crate::i::LinearMap::new())
    }

    /// Returns the number of elements that the map can hold
    ///
    /// Computes in **O(1)** time
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    /// use heapless::consts::*;
    ///
    /// let map: LinearMap<&str, isize, U8> = LinearMap::new();
    /// assert_eq!(map.capacity(), 8);
    /// ```
    pub fn capacity(&self) -> usize {
        N::to_usize()
    }

    /// Clears the map, removing all key-value pairs
    ///
    /// Computes in **O(1)** time
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    /// use heapless::consts::*;
    ///
    /// let mut map: LinearMap<_, _, U8> = LinearMap::new();
    /// map.insert(1, "a").unwrap();
    /// map.clear();
    /// assert!(map.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.0.buffer.clear()
    }

    /// Returns true if the map contains a value for the specified key.
    ///
    /// Computes in **O(N)** time
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    /// use heapless::consts::*;
    ///
    /// let mut map: LinearMap<_, _, U8> = LinearMap::new();
    /// map.insert(1, "a").unwrap();
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    pub fn contains_key(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    /// Returns a reference to the value corresponding to the key
    ///
    /// Computes in **O(N)** time
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    /// use heapless::consts::*;
    ///
    /// let mut map: LinearMap<_, _, U8> = LinearMap::new();
    /// map.insert(1, "a").unwrap();
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
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

    /// Returns a mutable reference to the value corresponding to the key
    ///
    /// Computes in **O(N)** time
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    /// use heapless::consts::*;
    ///
    /// let mut map: LinearMap<_, _, U8> = LinearMap::new();
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
        self.iter_mut()
            .find(|&(k, _)| k.borrow() == key)
            .map(|(_, v)| v)
    }

    /// Returns the number of elements in this map
    ///
    /// Computes in **O(1)** time
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    /// use heapless::consts::*;
    ///
    /// let mut a: LinearMap<_, _, U8> = LinearMap::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(1, "a").unwrap();
    /// assert_eq!(a.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.0.buffer.len
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old value is returned.
    ///
    /// Computes in **O(N)** time
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    /// use heapless::consts::*;
    ///
    /// let mut map: LinearMap<_, _, U8> = LinearMap::new();
    /// assert_eq!(map.insert(37, "a").unwrap(), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(37, "b").unwrap();
    /// assert_eq!(map.insert(37, "c").unwrap(), Some("b"));
    /// assert_eq!(map[&37], "c");
    /// ```
    pub fn insert(&mut self, key: K, mut value: V) -> Result<Option<V>, (K, V)> {
        if let Some((_, v)) = self.iter_mut().find(|&(k, _)| *k == key) {
            mem::swap(v, &mut value);
            return Ok(Some(value));
        }

        self.0.buffer.push((key, value))?;
        Ok(None)
    }

    /// Returns true if the map contains no elements
    ///
    /// Computes in **O(1)** time
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    /// use heapless::consts::*;
    ///
    /// let mut a: LinearMap<_, _, U8> = LinearMap::new();
    /// assert!(a.is_empty());
    /// a.insert(1, "a").unwrap();
    /// assert!(!a.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// An iterator visiting all key-value pairs in arbitrary order.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    /// use heapless::consts::*;
    ///
    /// let mut map: LinearMap<_, _, U8> = LinearMap::new();
    /// map.insert("a", 1).unwrap();
    /// map.insert("b", 2).unwrap();
    /// map.insert("c", 3).unwrap();
    ///
    /// for (key, val) in map.iter() {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            iter: self.0.buffer.as_slice().iter(),
        }
    }

    /// An iterator visiting all key-value pairs in arbitrary order, with mutable references to the
    /// values
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    /// use heapless::consts::*;
    ///
    /// let mut map: LinearMap<_, _, U8> = LinearMap::new();
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
            iter: self.0.buffer.as_mut_slice().iter_mut(),
        }
    }

    /// An iterator visiting all keys in arbitrary order
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    /// use heapless::consts::*;
    ///
    /// let mut map: LinearMap<_, _, U8> = LinearMap::new();
    /// map.insert("a", 1).unwrap();
    /// map.insert("b", 2).unwrap();
    /// map.insert("c", 3).unwrap();
    ///
    /// for key in map.keys() {
    ///     println!("{}", key);
    /// }
    /// ```
    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.iter().map(|(k, _)| k)
    }

    /// Removes a key from the map, returning the value at the key if the key was previously in the
    /// map
    ///
    /// Computes in **O(N)** time
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    /// use heapless::consts::*;
    ///
    /// let mut map: LinearMap<_, _, U8> = LinearMap::new();
    /// map.insert(1, "a").unwrap();
    /// assert_eq!(map.remove(&1), Some("a"));
    /// assert_eq!(map.remove(&1), None);
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

        idx.map(|idx| self.0.buffer.swap_remove(idx).1)
    }

    /// An iterator visiting all values in arbitrary order
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    /// use heapless::consts::*;
    ///
    /// let mut map: LinearMap<_, _, U8> = LinearMap::new();
    /// map.insert("a", 1).unwrap();
    /// map.insert("b", 2).unwrap();
    /// map.insert("c", 3).unwrap();
    ///
    /// for val in map.values() {
    ///     println!("{}", val);
    /// }
    /// ```
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.iter().map(|(_, v)| v)
    }

    /// An iterator visiting all values mutably in arbitrary order
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearMap;
    /// use heapless::consts::*;
    ///
    /// let mut map: LinearMap<_, _, U8> = LinearMap::new();
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
}

impl<'a, K, V, N, Q> ops::Index<&'a Q> for LinearMap<K, V, N>
where
    N: ArrayLength<(K, V)>,
    K: Borrow<Q> + Eq,
    Q: Eq + ?Sized,
{
    type Output = V;

    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("no entry found for key")
    }
}

impl<'a, K, V, N, Q> ops::IndexMut<&'a Q> for LinearMap<K, V, N>
where
    N: ArrayLength<(K, V)>,
    K: Borrow<Q> + Eq,
    Q: Eq + ?Sized,
{
    fn index_mut(&mut self, key: &Q) -> &mut V {
        self.get_mut(key).expect("no entry found for key")
    }
}

impl<K, V, N> Default for LinearMap<K, V, N>
where
    N: ArrayLength<(K, V)>,
    K: Eq,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V, N> Clone for LinearMap<K, V, N>
where
    N: ArrayLength<(K, V)>,
    K: Eq + Clone,
    V: Clone,
{
    fn clone(&self) -> Self {
        Self(crate::i::LinearMap {
            buffer: self.0.buffer.clone(),
        })
    }
}

impl<K, V, N> fmt::Debug for LinearMap<K, V, N>
where
    N: ArrayLength<(K, V)>,
    K: Eq + fmt::Debug,
    V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, V, N> FromIterator<(K, V)> for LinearMap<K, V, N>
where
    N: ArrayLength<(K, V)>,
    K: Eq,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (K, V)>,
    {
        let mut out = Self::new();
        out.0.buffer.extend(iter);
        out
    }
}

pub struct IntoIter<K, V, N>
where
    N: ArrayLength<(K, V)>,
    K: Eq,
{
    inner: <Vec<(K, V), N> as IntoIterator>::IntoIter,
}

impl<K, V, N> Iterator for IntoIter<K, V, N>
where
    N: ArrayLength<(K, V)>,
    K: Eq,
{
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<K, V, N> IntoIterator for LinearMap<K, V, N>
where
    N: ArrayLength<(K, V)>,
    K: Eq,
{
    type Item = (K, V);
    type IntoIter = IntoIter<K, V, N>;

    fn into_iter(mut self) -> Self::IntoIter {
        // FIXME this may result in a memcpy at runtime
        let lm = mem::replace(&mut self.0, unsafe { mem::uninitialized() });
        mem::forget(self);

        Self::IntoIter {
            inner: crate::Vec(lm.buffer).into_iter(),
        }
    }
}

impl<'a, K, V, N> IntoIterator for &'a LinearMap<K, V, N>
where
    N: ArrayLength<(K, V)>,
    K: Eq,
{
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub struct Iter<'a, K, V> {
    iter: slice::Iter<'a, (K, V)>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|&(ref k, ref v)| (k, v))
    }
}

impl<'a, K, V> Clone for Iter<'a, K, V> {
    fn clone(&self) -> Self {
        Self {
            iter: self.iter.clone(),
        }
    }
}

impl<K, V, N> Drop for LinearMap<K, V, N>
where
    N: ArrayLength<(K, V)>,
    K: Eq,
{
    fn drop(&mut self) {
        unsafe { ptr::drop_in_place(self.0.buffer.as_mut_slice()) }
    }
}

pub struct IterMut<'a, K, V> {
    iter: slice::IterMut<'a, (K, V)>,
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|&mut (ref k, ref mut v)| (k, v))
    }
}

impl<K, V, N, N2> PartialEq<LinearMap<K, V, N2>> for LinearMap<K, V, N>
where
    K: Eq,
    V: PartialEq,
    N: ArrayLength<(K, V)>,
    N2: ArrayLength<(K, V)>,
{
    fn eq(&self, other: &LinearMap<K, V, N2>) -> bool {
        self.len() == other.len()
            && self
                .iter()
                .all(|(key, value)| other.get(key).map_or(false, |v| *value == *v))
    }
}

impl<K, V, N> Eq for LinearMap<K, V, N>
where
    K: Eq,
    V: PartialEq,
    N: ArrayLength<(K, V)>,
{
}

#[cfg(test)]
mod test {
    use crate::{consts::*, LinearMap};

    #[test]
    fn static_new() {
        static mut _L: LinearMap<i32, i32, U8> = LinearMap(crate::i::LinearMap::new());
    }

    #[test]
    fn partial_eq() {
        {
            let mut a = LinearMap::<_, _, U1>::new();
            a.insert("k1", "v1").unwrap();

            let mut b = LinearMap::<_, _, U2>::new();
            b.insert("k1", "v1").unwrap();

            assert!(a == b);

            b.insert("k2", "v2").unwrap();

            assert!(a != b);
        }

        {
            let mut a = LinearMap::<_, _, U2>::new();
            a.insert("k1", "v1").unwrap();
            a.insert("k2", "v2").unwrap();

            let mut b = LinearMap::<_, _, U2>::new();
            b.insert("k2", "v2").unwrap();
            b.insert("k1", "v1").unwrap();

            assert!(a == b);
        }
    }
}

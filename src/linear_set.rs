//! A fixed capacity set that performs lookups via linear search.
//!
//! No hashing is used, so most operations are *O*(n) instead of *O*(1).

use core::{borrow::Borrow, fmt, iter::FusedIterator};

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

use crate::{
    linear_map::{self, LinearMapInner, LinearMapStorage, OwnedStorage, ViewStorage},
    LinearMap,
};

/// Base struct for [`LinearSet`] and [`LinearSetView`]
#[cfg_attr(
    feature = "zeroize",
    derive(Zeroize),
    zeroize(bound = "S: Zeroize, T: Zeroize")
)]
pub struct LinearSetInner<T, S: LinearMapStorage<T, ()> + ?Sized> {
    pub(crate) map: LinearMapInner<T, (), S>,
}

/// A fixed capacity set that performs lookups via linear search.
///
/// Note that as this set doesn't use hashing so most operations are *O*(n) instead of *O*(1).
pub type LinearSet<T, const N: usize> = LinearSetInner<T, OwnedStorage<T, (), N>>;

/// A dynamic capacity set that performs lookups via linear search.
///
/// Note that as this set doesn't use hashing so most operations are *O*(n) instead of *O*(1).
pub type LinearSetView<T> = LinearSetInner<T, ViewStorage<T, ()>>;

impl<T, const N: usize> LinearSet<T, N> {
    /// Creates an empty `LinearSet`.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearSet;
    ///
    /// // allocate the set on the stack
    /// let mut set: LinearSet<&str, 8> = LinearSet::new();
    ///
    /// // allocate the set in a static variable
    /// static mut SET: LinearSet<&str, 8> = LinearSet::new();
    /// ```
    pub const fn new() -> Self {
        Self {
            map: LinearMap::new(),
        }
    }
}

impl<T, S: LinearMapStorage<T, ()> + ?Sized> LinearSetInner<T, S>
where
    T: Eq,
{
    /// Returns the number of elements that the set can hold.
    ///
    /// Computes in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearSet;
    ///
    /// let map: LinearSet<&str, 8> = LinearSet::new();
    /// assert_eq!(map.capacity(), 8);
    /// ```
    pub fn capacity(&self) -> usize {
        self.map.capacity()
    }

    /// Clears the set, removing all values.
    ///
    /// Computes in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearSet;
    ///
    /// let mut set: LinearSet<_, 8> = LinearSet::new();
    /// set.insert("a").unwrap();
    /// set.clear();
    /// assert!(set.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.map.clear();
    }

    /// Returns true if the set contains a value for the specified key.
    ///
    /// Computes in *O*(n) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearSet;
    ///
    /// let mut set: LinearSet<_, 8> = LinearSet::new();
    /// set.insert("a").unwrap();
    /// assert_eq!(set.contains(&"a"), true);
    /// assert_eq!(set.contains(&"b"), false);
    /// ```
    pub fn contains(&self, value: &T) -> bool {
        self.map.contains_key(value)
    }

    /// Returns a reference to the element in the set, if any, that is is equal
    /// to the value.
    ///
    /// Computes in *O*(n) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearSet;
    ///
    /// let mut set: LinearSet<_, 8> = LinearSet::new();
    /// set.insert("a").unwrap();
    /// assert_eq!(set.get(&"a"), Some(&"a"));
    /// assert_eq!(set.get(&"b"), None);
    /// ```
    pub fn get<Q>(&self, value: &Q) -> Option<&T>
    where
        T: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.map
            .iter()
            .find(|&(k, ())| k.borrow() == value)
            .map(|(k, ())| k)
    }

    /// Returns the number of elements in this set.
    ///
    /// Computes in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearSet;
    ///
    /// let mut a: LinearSet<_, 8> = LinearSet::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert("a").unwrap();
    /// assert_eq!(a.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Inserts a value into the set.
    ///
    /// If the set did not have this value present, `true` is returned.
    ///
    /// If the set did have this value present, `false` is returned.
    ///
    /// Computes in *O*(n) time
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearSet;
    ///
    /// let mut set = LinearSet::<_, 16>::new();
    ///
    /// assert_eq!(set.insert(2).unwrap(), true);
    /// assert_eq!(set.insert(2).unwrap(), false);
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn insert(&mut self, value: T) -> Result<bool, T> {
        self.map
            .insert(value, ())
            .map(|old| old.is_none())
            .map_err(|(k, ())| k)
    }

    /// Returns true if the set contains no elements.
    ///
    /// Computes in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearSet;
    ///
    /// let mut a: LinearSet<_, 8> = LinearSet::new();
    /// assert!(a.is_empty());
    /// a.insert("a").unwrap();
    /// assert!(!a.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Returns true if the set is full.
    ///
    /// Computes in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearSet;
    ///
    /// let mut a: LinearSet<_, 4> = LinearSet::new();
    /// assert!(!a.is_full());
    /// a.insert("a").unwrap();
    /// a.insert("b").unwrap();
    /// a.insert("c").unwrap();
    /// a.insert("d").unwrap();
    /// assert!(a.is_full());
    /// ```
    pub fn is_full(&self) -> bool {
        self.map.is_full()
    }

    /// An iterator visiting all values in arbitrary order.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearSet;
    ///
    /// let mut set = LinearSet::<_, 16>::new();
    /// set.insert("a").unwrap();
    /// set.insert("b").unwrap();
    ///
    /// for x in set.iter() {
    ///     println!("{}", x);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            iter: self.map.iter(),
        }
    }

    /// Removes a value from the set. Returns `true` if the value was present in
    /// the set.
    ///
    /// Computes in *O*(n) time
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::LinearSet;
    ///
    /// let mut set: LinearSet<_, 8> = LinearSet::new();
    /// set.insert("a").unwrap();
    /// assert_eq!(set.remove(&"a"), true);
    /// assert_eq!(set.remove(&"a"), false);
    /// ```
    pub fn remove<Q>(&mut self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Eq + ?Sized,
    {
        self.map.remove(value).is_some()
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` for which `f(&e)` returns `false`.
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.map.retain(move |k, ()| f(k));
    }
}

impl<T, const N: usize> Default for LinearSet<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const N: usize> Clone for LinearSet<T, N>
where
    T: Eq + Clone,
{
    fn clone(&self) -> Self {
        Self {
            map: self.map.clone(),
        }
    }
}

impl<T, S: LinearMapStorage<T, ()> + ?Sized> fmt::Debug for LinearSetInner<T, S>
where
    T: Eq + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl<T, const N: usize> FromIterator<T> for LinearSet<T, N> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let mut set = Self::default();
        set.map.buffer.extend(iter.into_iter().map(|k| (k, ())));
        set
    }
}

/// An iterator that moves out of a [`LinearSet`].
///
/// This struct is created by calling the [`into_iter`](LinearSet::into_iter) method on
/// [`LinearSet`].
pub struct IntoIter<T, const N: usize>
where
    T: Eq,
{
    iter: linear_map::IntoIter<T, (), N>,
}

impl<T, const N: usize> Iterator for IntoIter<T, N>
where
    T: Eq,
{
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(k, ())| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }
}

impl<T, const N: usize> FusedIterator for IntoIter<T, N> where T: Eq {}

impl<T, const N: usize> ExactSizeIterator for IntoIter<T, N>
where
    T: Eq,
{
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<T, const N: usize> IntoIterator for LinearSet<T, N>
where
    T: Eq,
{
    type Item = T;
    type IntoIter = IntoIter<T, N>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            iter: self.map.into_iter(),
        }
    }
}

impl<'a, T, S: LinearMapStorage<T, ()> + ?Sized> IntoIterator for &'a LinearSetInner<T, S>
where
    T: Eq,
{
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// An iterator over the items of a [`LinearSet`].
///
/// This `struct` is created by the [`iter`](LinearSet::iter) method on
/// [`LinearSet`]. See its documentation for more.
#[derive(Clone, Debug)]
pub struct Iter<'a, T> {
    iter: linear_map::Iter<'a, T, ()>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(k, ())| k)
    }
}

impl<T, S1: LinearMapStorage<T, ()> + ?Sized, S2: LinearMapStorage<T, ()> + ?Sized>
    PartialEq<LinearSetInner<T, S2>> for LinearSetInner<T, S1>
where
    T: Eq,
{
    fn eq(&self, other: &LinearSetInner<T, S2>) -> bool {
        self.len() == other.len()
            && self
                .iter()
                .all(|value| other.get(value).is_some_and(|v| *value == *v))
    }
}

impl<T, S: LinearMapStorage<T, ()> + ?Sized> Eq for LinearSetInner<T, S> where T: Eq {}

#[cfg(test)]
mod test {
    use static_assertions::assert_not_impl_any;

    use crate::LinearSet;

    // Ensure a `LinearSet` containing `!Send` keys stays `!Send` itself.
    assert_not_impl_any!(LinearSet<*const (),  4>: Send);
    // Ensure a `LinearSet` containing `!Send` values stays `!Send` itself.
    assert_not_impl_any!(LinearSet<*const (), 4>: Send);

    #[test]
    fn static_new() {
        static mut _L: LinearSet<i32, 8> = LinearSet::new();
    }

    #[test]
    fn borrow() {
        use crate::String;

        let mut set = LinearSet::<_, 8>::new();

        let s = String::<64>::try_from("Hello, world!").unwrap();
        set.insert(s).unwrap();

        assert_eq!(set.get("Hello, world!").unwrap(), &"Hello, world!");
    }

    #[test]
    fn partial_eq() {
        {
            let mut a = LinearSet::<_, 1>::new();
            a.insert("v1").unwrap();

            let mut b = LinearSet::<_, 2>::new();
            b.insert("v1").unwrap();

            assert!(a == b);

            b.insert("v2").unwrap();

            assert!(a != b);
        }

        {
            let mut a = LinearSet::<_, 2>::new();
            a.insert("v1").unwrap();
            a.insert("v2").unwrap();

            let mut b = LinearSet::<_, 2>::new();
            b.insert("v2").unwrap();
            b.insert("v1").unwrap();

            assert!(a == b);
        }
    }

    #[test]
    fn into_iter() {
        let mut src: LinearSet<_, 4> = LinearSet::new();
        src.insert("v1").unwrap();
        src.insert("v2").unwrap();
        src.insert("v3").unwrap();
        src.insert("v4").unwrap();
        let clone = src.clone();
        for v in clone.into_iter() {
            src.remove(v);
        }
        assert!(src.is_empty());
    }

    #[test]
    fn into_iter_len() {
        let mut src: LinearSet<_, 2> = LinearSet::new();
        src.insert("v1").unwrap();
        src.insert("v2").unwrap();
        let mut items = src.into_iter();
        assert_eq!(items.len(), 2);
        let _ = items.next();
        assert_eq!(items.len(), 1);
        let _ = items.next();
        assert_eq!(items.len(), 0);
    }

    #[test]
    fn partial_eq_floats() {
        // Make sure `PartialEq` is implemented even if `V` doesn't implement `Eq`.
        let set: LinearSet<usize, 4> = Default::default();
        assert_eq!(set, set);
    }

    #[test]
    #[cfg(feature = "zeroize")]
    fn test_linear_map_zeroize() {
        use zeroize::Zeroize;

        let mut set: LinearSet<u8, 8> = LinearSet::new();
        for i in 1..=8 {
            set.insert(i).unwrap();
        }

        assert_eq!(set.len(), 8);
        assert_eq!(set.get(&5), Some(&5));

        // zeroized using Vec's implementation
        set.zeroize();

        assert_eq!(set.len(), 0);
        assert!(set.is_empty());
    }

    // tests that use this constant take too long to run under miri, specially on CI, with a map of
    // this size so make the map smaller when using miri
    #[cfg(not(miri))]
    const SET_SLOTS: usize = 4096;
    #[cfg(miri)]
    const SET_SLOTS: usize = 64;
    fn almost_filled_set() -> LinearSet<usize, SET_SLOTS> {
        let mut almost_filled = LinearSet::new();
        for i in 1..SET_SLOTS {
            almost_filled.insert(i).unwrap();
        }
        almost_filled
    }

    #[test]
    fn remove() {
        let mut src = almost_filled_set();
        // value doesn't exist
        let v = 0;
        let r = src.remove(&v);
        assert!(!r);

        let v = 5;
        let r = src.remove(&v);
        assert!(r);
        let r = src.remove(&v);
        assert!(!r);
        assert_eq!(src.len(), SET_SLOTS - 2);
    }

    #[test]
    fn retain() {
        let mut src = almost_filled_set();
        src.retain(|v| v % 2 == 0);
        src.retain(|v| v % 3 == 0);

        for v in src.iter() {
            assert_eq!(v % 2, 0);
            assert_eq!(v % 3, 0);
        }

        let mut src = almost_filled_set();
        src.retain(|_v| false);
        assert!(src.is_empty());

        let mut src = almost_filled_set();
        src.retain(|_v| true);
        assert_eq!(src.len(), SET_SLOTS - 1);
        src.insert(0).unwrap();
        src.retain(|_v| true);
        assert_eq!(src.len(), SET_SLOTS);
    }
}

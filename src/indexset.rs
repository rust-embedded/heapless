use core::{borrow::Borrow, fmt, iter::FromIterator};

use generic_array::{typenum::PowerOfTwo, ArrayLength};
use hash32::{BuildHasher, BuildHasherDefault, FnvHasher, Hash, Hasher};

use crate::indexmap::{self, Bucket, IndexMap, Pos};

/// An `IndexSet` using the default FNV hasher
pub type FnvIndexSet<T, N> = IndexSet<T, N, BuildHasherDefault<FnvHasher>>;

/// Fixed capacity [`IndexSet`](https://docs.rs/indexmap/1/indexmap/set/struct.IndexSet.html)
///
/// Note that the capacity of the `IndexSet` must be a power of 2.
///
/// # Examples
///
/// ```
/// use heapless::FnvIndexSet;
/// use heapless::consts::*;
///
/// // A hash set with a capacity of 16 elements allocated on the stack
/// let mut books = FnvIndexSet::<_, U16>::new();
///
/// // Add some books.
/// books.insert("A Dance With Dragons").unwrap();
/// books.insert("To Kill a Mockingbird").unwrap();
/// books.insert("The Odyssey").unwrap();
/// books.insert("The Great Gatsby").unwrap();
///
/// // Check for a specific one.
/// if !books.contains("The Winds of Winter") {
///     println!("We have {} books, but The Winds of Winter ain't one.",
///              books.len());
/// }
///
/// // Remove a book.
/// books.remove("The Odyssey");
///
/// // Iterate over everything.
/// for book in &books {
///     println!("{}", book);
/// }
/// ```
pub struct IndexSet<T, N, S>
where
    T: Eq + Hash,
    N: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>>,
{
    map: IndexMap<T, (), N, S>,
}

impl<T, N, S> IndexSet<T, N, BuildHasherDefault<S>>
where
    T: Eq + Hash,
    S: Default + Hasher,
    N: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>> + PowerOfTwo,
{
    /// Creates an empty `IndexSet`
    pub fn new() -> Self {
        IndexSet {
            map: IndexMap::new(),
        }
    }
}

impl<T, N, S> IndexSet<T, N, S>
where
    T: Eq + Hash,
    S: BuildHasher,
    N: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>>,
{
    /// Returns the number of elements the set can hold
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::FnvIndexSet;
    /// use heapless::consts::*;
    ///
    /// let set = FnvIndexSet::<i32, U16>::new();
    /// assert_eq!(set.capacity(), 16);
    /// ```
    pub fn capacity(&self) -> usize {
        self.map.capacity()
    }

    /// Return an iterator over the values of the set, in their order
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::FnvIndexSet;
    /// use heapless::consts::*;
    ///
    /// let mut set = FnvIndexSet::<_, U16>::new();
    /// set.insert("a").unwrap();
    /// set.insert("b").unwrap();
    ///
    /// // Will print in an arbitrary order.
    /// for x in set.iter() {
    ///     println!("{}", x);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            iter: self.map.iter(),
        }
    }

    /// Visits the values representing the difference, i.e. the values that are in `self` but not in
    /// `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::FnvIndexSet;
    /// use heapless::consts::*;
    ///
    /// let mut a: FnvIndexSet<_, U16> = [1, 2, 3].iter().cloned().collect();
    /// let mut b: FnvIndexSet<_, U16> = [4, 2, 3, 4].iter().cloned().collect();
    ///
    /// // Can be seen as `a - b`.
    /// for x in a.difference(&b) {
    ///     println!("{}", x); // Print 1
    /// }
    ///
    /// let diff: FnvIndexSet<_, U16> = a.difference(&b).collect();
    /// assert_eq!(diff, [1].iter().collect::<FnvIndexSet<_, U16>>());
    ///
    /// // Note that difference is not symmetric,
    /// // and `b - a` means something else:
    /// let diff: FnvIndexSet<_, U16> = b.difference(&a).collect();
    /// assert_eq!(diff, [4].iter().collect::<FnvIndexSet<_, U16>>());
    /// ```
    pub fn difference<'a, N2, S2>(
        &'a self,
        other: &'a IndexSet<T, N2, S2>,
    ) -> Difference<'a, T, N2, S2>
    where
        N2: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>>,
        S2: BuildHasher,
    {
        Difference {
            iter: self.iter(),
            other,
        }
    }

    /// Visits the values representing the symmetric difference, i.e. the values that are in `self`
    /// or in `other` but not in both.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::FnvIndexSet;
    /// use heapless::consts::*;
    ///
    /// let mut a: FnvIndexSet<_, U16> = [1, 2, 3].iter().cloned().collect();
    /// let mut b: FnvIndexSet<_, U16> = [4, 2, 3, 4].iter().cloned().collect();
    ///
    /// // Print 1, 4 in that order order.
    /// for x in a.symmetric_difference(&b) {
    ///     println!("{}", x);
    /// }
    ///
    /// let diff1: FnvIndexSet<_, U16> = a.symmetric_difference(&b).collect();
    /// let diff2: FnvIndexSet<_, U16> = b.symmetric_difference(&a).collect();
    ///
    /// assert_eq!(diff1, diff2);
    /// assert_eq!(diff1, [1, 4].iter().collect::<FnvIndexSet<_, U16>>());
    /// ```
    pub fn symmetric_difference<'a, N2, S2>(
        &'a self,
        other: &'a IndexSet<T, N2, S2>,
    ) -> impl Iterator<Item = &'a T>
    where
        N2: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>>,
        S2: BuildHasher,
    {
        self.difference(other).chain(other.difference(self))
    }

    /// Visits the values representing the intersection, i.e. the values that are both in `self` and
    /// `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::FnvIndexSet;
    /// use heapless::consts::*;
    ///
    /// let mut a: FnvIndexSet<_, U16> = [1, 2, 3].iter().cloned().collect();
    /// let mut b: FnvIndexSet<_, U16> = [4, 2, 3, 4].iter().cloned().collect();
    ///
    /// // Print 2, 3 in that order.
    /// for x in a.intersection(&b) {
    ///     println!("{}", x);
    /// }
    ///
    /// let intersection: FnvIndexSet<_, U16> = a.intersection(&b).collect();
    /// assert_eq!(intersection, [2, 3].iter().collect::<FnvIndexSet<_, U16>>());
    /// ```
    pub fn intersection<'a, N2, S2>(
        &'a self,
        other: &'a IndexSet<T, N2, S2>,
    ) -> Intersection<'a, T, N2, S2>
    where
        N2: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>>,
        S2: BuildHasher,
    {
        Intersection {
            iter: self.iter(),
            other,
        }
    }

    /// Visits the values representing the union, i.e. all the values in `self` or `other`, without
    /// duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::FnvIndexSet;
    /// use heapless::consts::*;
    ///
    /// let mut a: FnvIndexSet<_, U16> = [1, 2, 3].iter().cloned().collect();
    /// let mut b: FnvIndexSet<_, U16> = [4, 2, 3, 4].iter().cloned().collect();
    ///
    /// // Print 1, 2, 3, 4 in that order.
    /// for x in a.union(&b) {
    ///     println!("{}", x);
    /// }
    ///
    /// let union: FnvIndexSet<_, U16> = a.union(&b).collect();
    /// assert_eq!(union, [1, 2, 3, 4].iter().collect::<FnvIndexSet<_, U16>>());
    /// ```
    pub fn union<'a, N2, S2>(
        &'a self,
        other: &'a IndexSet<T, N2, S2>,
    ) -> impl Iterator<Item = &'a T>
    where
        N2: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>>,
        S2: BuildHasher,
    {
        self.iter().chain(other.difference(self))
    }

    /// Returns the number of elements in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::FnvIndexSet;
    /// use heapless::consts::*;
    ///
    /// let mut v: FnvIndexSet<_, U16> = FnvIndexSet::new();
    /// assert_eq!(v.len(), 0);
    /// v.insert(1).unwrap();
    /// assert_eq!(v.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns `true` if the set contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::FnvIndexSet;
    /// use heapless::consts::*;
    ///
    /// let mut v: FnvIndexSet<_, U16> = FnvIndexSet::new();
    /// assert!(v.is_empty());
    /// v.insert(1).unwrap();
    /// assert!(!v.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Clears the set, removing all values.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::FnvIndexSet;
    /// use heapless::consts::*;
    ///
    /// let mut v: FnvIndexSet<_, U16> = FnvIndexSet::new();
    /// v.insert(1).unwrap();
    /// v.clear();
    /// assert!(v.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.map.clear()
    }

    /// Returns `true` if the set contains a value.
    ///
    /// The value may be any borrowed form of the set's value type, but `Hash` and `Eq` on the
    /// borrowed form must match those for the value type.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::FnvIndexSet;
    /// use heapless::consts::*;
    ///
    /// let set: FnvIndexSet<_, U16> = [1, 2, 3].iter().cloned().collect();
    /// assert_eq!(set.contains(&1), true);
    /// assert_eq!(set.contains(&4), false);
    /// ```
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: ?Sized + Eq + Hash,
    {
        self.map.contains_key(value)
    }

    /// Returns `true` if `self` has no elements in common with `other`. This is equivalent to
    /// checking for an empty intersection.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::FnvIndexSet;
    /// use heapless::consts::*;
    ///
    /// let a: FnvIndexSet<_, U16> = [1, 2, 3].iter().cloned().collect();
    /// let mut b = FnvIndexSet::<_, U16>::new();
    ///
    /// assert_eq!(a.is_disjoint(&b), true);
    /// b.insert(4).unwrap();
    /// assert_eq!(a.is_disjoint(&b), true);
    /// b.insert(1).unwrap();
    /// assert_eq!(a.is_disjoint(&b), false);
    /// ```
    pub fn is_disjoint<N2, S2>(&self, other: &IndexSet<T, N2, S2>) -> bool
    where
        N2: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>>,
        S2: BuildHasher,
    {
        self.iter().all(|v| !other.contains(v))
    }

    /// Returns `true` if the set is a subset of another, i.e. `other` contains at least all the
    /// values in `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::FnvIndexSet;
    /// use heapless::consts::*;
    ///
    /// let sup: FnvIndexSet<_, U16> = [1, 2, 3].iter().cloned().collect();
    /// let mut set = FnvIndexSet::<_, U16>::new();
    ///
    /// assert_eq!(set.is_subset(&sup), true);
    /// set.insert(2).unwrap();
    /// assert_eq!(set.is_subset(&sup), true);
    /// set.insert(4).unwrap();
    /// assert_eq!(set.is_subset(&sup), false);
    /// ```
    pub fn is_subset<N2, S2>(&self, other: &IndexSet<T, N2, S2>) -> bool
    where
        N2: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>>,
        S2: BuildHasher,
    {
        self.iter().all(|v| other.contains(v))
    }

    // Returns `true` if the set is a superset of another, i.e. `self` contains at least all the
    // values in `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::FnvIndexSet;
    /// use heapless::consts::*;
    ///
    /// let sub: FnvIndexSet<_, U16> = [1, 2].iter().cloned().collect();
    /// let mut set = FnvIndexSet::<_, U16>::new();
    ///
    /// assert_eq!(set.is_superset(&sub), false);
    ///
    /// set.insert(0).unwrap();
    /// set.insert(1).unwrap();
    /// assert_eq!(set.is_superset(&sub), false);
    ///
    /// set.insert(2).unwrap();
    /// assert_eq!(set.is_superset(&sub), true);
    /// ```
    pub fn is_superset<N2, S2>(&self, other: &IndexSet<T, N2, S2>) -> bool
    where
        N2: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>>,
        S2: BuildHasher,
    {
        other.is_subset(self)
    }

    /// Adds a value to the set.
    ///
    /// If the set did not have this value present, `true` is returned.
    ///
    /// If the set did have this value present, `false` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::FnvIndexSet;
    /// use heapless::consts::*;
    ///
    /// let mut set = FnvIndexSet::<_, U16>::new();
    ///
    /// assert_eq!(set.insert(2).unwrap(), true);
    /// assert_eq!(set.insert(2).unwrap(), false);
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn insert(&mut self, value: T) -> Result<bool, T> {
        self.map
            .insert(value, ())
            .map(|old| old.is_none())
            .map_err(|(k, _)| k)
    }

    /// Removes a value from the set. Returns `true` if the value was present in the set.
    ///
    /// The value may be any borrowed form of the set's value type, but `Hash` and `Eq` on the
    /// borrowed form must match those for the value type.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::FnvIndexSet;
    /// use heapless::consts::*;
    ///
    /// let mut set = FnvIndexSet::<_, U16>::new();
    ///
    /// set.insert(2).unwrap();
    /// assert_eq!(set.remove(&2), true);
    /// assert_eq!(set.remove(&2), false);
    /// ```
    pub fn remove<Q>(&mut self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: ?Sized + Eq + Hash,
    {
        self.map.remove(value).is_some()
    }
}

impl<T, N, S> Clone for IndexSet<T, N, S>
where
    T: Eq + Hash + Clone,
    S: Clone,
    N: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>>,
{
    fn clone(&self) -> Self {
        Self {
            map: self.map.clone(),
        }
    }
}

impl<T, N, S> fmt::Debug for IndexSet<T, N, S>
where
    T: Eq + Hash + fmt::Debug,
    S: BuildHasher,
    N: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl<T, N, S> Default for IndexSet<T, N, S>
where
    T: Eq + Hash,
    S: BuildHasher + Default,
    N: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>>,
{
    fn default() -> Self {
        IndexSet {
            map: <_>::default(),
        }
    }
}

impl<T, N1, N2, S1, S2> PartialEq<IndexSet<T, N2, S2>> for IndexSet<T, N1, S1>
where
    T: Eq + Hash,
    S1: BuildHasher,
    S2: BuildHasher,
    N1: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>>,
    N2: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>>,
{
    fn eq(&self, other: &IndexSet<T, N2, S2>) -> bool {
        self.len() == other.len() && self.is_subset(other)
    }
}

impl<T, N, S> Extend<T> for IndexSet<T, N, S>
where
    T: Eq + Hash,
    S: BuildHasher,
    N: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>>,
{
    fn extend<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = T>,
    {
        self.map.extend(iterable.into_iter().map(|k| (k, ())))
    }
}

impl<'a, T, N, S> Extend<&'a T> for IndexSet<T, N, S>
where
    T: 'a + Eq + Hash + Copy,
    S: BuildHasher,
    N: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>>,
{
    fn extend<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = &'a T>,
    {
        self.extend(iterable.into_iter().cloned())
    }
}

impl<T, N, S> FromIterator<T> for IndexSet<T, N, S>
where
    T: Eq + Hash,
    S: BuildHasher + Default,
    N: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>>,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let mut set = IndexSet::default();
        set.extend(iter);
        set
    }
}

impl<'a, T, N, S> IntoIterator for &'a IndexSet<T, N, S>
where
    T: Eq + Hash,
    S: BuildHasher,
    N: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>>,
{
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub struct Iter<'a, T> {
    iter: indexmap::Iter<'a, T, ()>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(k, _)| k)
    }
}

impl<'a, T> Clone for Iter<'a, T> {
    fn clone(&self) -> Self {
        Self {
            iter: self.iter.clone(),
        }
    }
}

pub struct Difference<'a, T, N, S>
where
    S: BuildHasher,
    T: Eq + Hash,
    N: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>>,
{
    iter: Iter<'a, T>,
    other: &'a IndexSet<T, N, S>,
}

impl<'a, T, N, S> Iterator for Difference<'a, T, N, S>
where
    S: BuildHasher,
    T: Eq + Hash,
    N: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>>,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let elt = self.iter.next()?;
            if !self.other.contains(elt) {
                return Some(elt);
            }
        }
    }
}

pub struct Intersection<'a, T, N, S>
where
    S: BuildHasher,
    T: Eq + Hash,
    N: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>>,
{
    iter: Iter<'a, T>,
    other: &'a IndexSet<T, N, S>,
}

impl<'a, T, N, S> Iterator for Intersection<'a, T, N, S>
where
    S: BuildHasher,
    T: Eq + Hash,
    N: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>>,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let elt = self.iter.next()?;
            if self.other.contains(elt) {
                return Some(elt);
            }
        }
    }
}

use core::borrow::Borrow;
use core::iter::FromIterator;
use core::{fmt, ops, slice};

use generic_array::typenum::PowerOfTwo;
use generic_array::{ArrayLength, GenericArray};

use hash32::{BuildHasher, BuildHasherDefault, FnvHasher, Hash, Hasher};

use Vec;
use __core::mem;

/// An `IndexMap` using the default FNV hasher
pub type FnvIndexMap<K, V, N> = IndexMap<K, V, N, BuildHasherDefault<FnvHasher>>;

#[derive(Clone, Copy, Eq, PartialEq)]
struct HashValue(u16);

impl HashValue {
    fn desired_pos(&self, mask: usize) -> usize {
        usize::from(self.0) & mask
    }

    fn probe_distance(&self, mask: usize, current: usize) -> usize {
        current.wrapping_sub(self.desired_pos(mask) as usize) & mask
    }
}

#[doc(hidden)]
pub struct Bucket<K, V> {
    hash: HashValue,
    key: K,
    value: V,
}

#[doc(hidden)]
#[derive(Clone, Copy, PartialEq)]
pub struct Pos {
    // compact representation of `{ hash_value: u16, index: u16 }`
    // stores hash<<16 + index + 1,
    // such that 0x00000000 can be used for optimization
    combined: u32,
}

impl Pos {
    fn new(index: usize, hash: HashValue) -> Self {
        Pos {
            combined: ((u32::from(hash.0) << 16) + index as u32).wrapping_add(1)
        }
    }

    fn hash(&self) -> HashValue {
        HashValue((self.combined.wrapping_sub(1) >> 16) as u16)
    }

    fn index(&self) -> usize {
        self.combined.wrapping_sub(1) as u16 as usize
    }

}

#[doc(hidden)]
#[derive(Clone, Copy, PartialEq)]
// optional representation of `Pos`
// the unlikely combined value of `{ hash_value: 0xffff, index: 0xffff } + 1`,
// which is 0x00000000, is used to represent None,
// instead of the more likely of `{ hash_value: 0x00, index: 0x00 } + 1`
pub struct OptionalPos(Pos);

impl OptionalPos {
    const MAGIC_NONE: u32 = 0x00000000;

    fn some(index: usize, hash: HashValue) -> Result<Self, ()> {
        Self::some_from_pos(Pos::new(index, hash))
    }

    fn some_from_pos(pos: Pos) -> Result<Self, ()> {
        let opt = OptionalPos(pos);
        if opt.is_some() {
            Ok(opt)
        } else {
            Err(())
        }
    }

    fn none() -> Self {
        OptionalPos(
            Pos {
                combined: Self::MAGIC_NONE
            }
        )
    }

    fn is_some(&self) -> bool {
        !self.is_none()
    }

    fn is_none(&self) -> bool {
        self.0.combined == Self::MAGIC_NONE
    }

    fn hash(&self) -> Option<HashValue> {
        if self.is_some() {
            Some(self.0.hash())
        } else {
            None
        }
    }

    fn index(&self) -> Option<usize> {
        if self.is_some() {
            Some(self.0.index())
        } else {
            None
        }
    }
}


pub enum Inserted<V> {
    Done,
    Swapped { prev_value: V },
    RobinHood { probe: usize, old_pos: Pos },
}

macro_rules! probe_loop {
    ($probe_var: ident < $len: expr, $body: expr) => {
        loop {
            if $probe_var < $len {
                $body
                    $probe_var += 1;
            } else {
                $probe_var = 0;
            }
        }
    }
}

struct CoreMap<K, V, N>
where
    K: Eq + Hash,
    N: ArrayLength<Bucket<K, V>> + ArrayLength<OptionalPos>,
{
    entries: Vec<Bucket<K, V>, N>,
    indices: GenericArray<OptionalPos, N>,
}

impl<K, V, N> CoreMap<K, V, N>
where
    K: Eq + Hash,
    N: ArrayLength<Bucket<K, V>> + ArrayLength<OptionalPos>,
{
    // TODO turn into a `const fn`; needs `mem::zeroed` to be a `const fn`
    fn new() -> Self {
        CoreMap {
            entries: Vec::new(),
            // zeroed memory represents [None ...]
            indices: unsafe { mem::zeroed() },
        }
    }

    fn capacity() -> usize {
        N::to_usize()
    }

    fn mask() -> usize {
        Self::capacity() - 1
    }

    fn find<Q>(&self, hash: HashValue, query: &Q) -> Option<(usize, usize)>
    where
        K: Borrow<Q>,
        Q: ?Sized + Eq,
    {
        let mut probe = hash.desired_pos(Self::mask());
        let mut dist = 0;

        probe_loop!(probe < self.indices.len(), {
            let pos: OptionalPos = self.indices[probe];
            if pos.is_some() {
                let entry_hash = pos.hash().unwrap();
                // NOTE(i) we use unchecked indexing below
                let i = pos.index().unwrap();
                debug_assert!(i < self.entries.len());

                if dist > entry_hash.probe_distance(Self::mask(), probe) {
                    // give up when probe distance is too long
                    return None;
                } else if entry_hash == hash && unsafe {
                    self.entries.get_unchecked(i).key.borrow() == query
                } {
                    return Some((probe, i));
                }
            } else {
                return None;
            }

            dist += 1;
        });
    }

    // First phase: Look for the preferred location for key.
    //
    // We will know if `key` is already in the map, before we need to insert it.
    // When we insert they key, it might be that we need to continue displacing
    // entries (robin hood hashing), in which case Inserted::RobinHood is returned
    fn insert_phase_1(&mut self, hash: HashValue, key: K, value: V) -> Inserted<V> {
        let mut probe = hash.desired_pos(Self::mask());
        let mut dist = 0;

        let inserted;
        probe_loop!(probe < self.indices.len(), {
            let pos: &mut OptionalPos = &mut self.indices[probe];

            if pos.is_some() {
                let entry_hash = pos.hash().unwrap();
                // NOTE(i) we use unchecked indexing below
                let i = pos.index().unwrap();
                debug_assert!(i < self.entries.len());

                let their_dist = entry_hash.probe_distance(Self::mask(), probe);

                if their_dist < dist {
                    // robin hood: steal the spot if it's better for us
                    let index = self.entries.len();
                    inserted = Inserted::RobinHood {
                        probe: probe,
                        old_pos: Pos::new(index, hash),
                    };
                    break;
                } else if entry_hash == hash && unsafe { self.entries.get_unchecked(i).key == key }
                {
                    return Inserted::Swapped {
                        prev_value: mem::replace(
                            unsafe { &mut self.entries.get_unchecked_mut(i).value },
                            value,
                        ),
                    };
                }
            } else {
                // empty bucket, insert here
                let index = self.entries.len();
                // FIXME unwrap is actually unsafe here
                // FIXME when the combined index and hash happen to be 0xffffffff
                *pos = OptionalPos::some(index, hash).unwrap();
                inserted = Inserted::Done;
                break;
            }
            dist += 1;
        });

        // NOTE(unsafe) we already checked (in `insert`) that we aren't exceeding the capacity
        unsafe { self.entries.push_unchecked(Bucket { hash, key, value }) }
        inserted
    }

    // phase 2 is post-insert where we forward-shift `Pos` in the indices.
    fn insert_phase_2(&mut self, mut probe: usize, mut old_pos: Pos) {
        probe_loop!(probe < self.indices.len(), {
            let pos: &mut OptionalPos = unsafe { self.indices.get_unchecked_mut(probe) };
            if pos.is_some() {
                // swaps pos and old_pos, leavs a valid Pos in both,
                // since both are implicitly of OptionalPos::some
                old_pos = mem::replace(&mut pos.0, old_pos)
            } else {
                *pos = OptionalPos::some_from_pos(old_pos).unwrap();
                break;
            }
        });
    }

    fn remove_found(&mut self, probe: usize, found: usize) -> (K, V) {
        // index `probe` and entry `found` is to be removed
        // use swap_remove, but then we need to update the index that points
        // to the other entry that has to move
        self.indices[probe] = OptionalPos::none();
        let entry = unsafe { self.entries.swap_remove_unchecked(found) };

        // correct index that points to the entry that had to swap places
        if let Some(entry) = self.entries.get(found) {
            // was not last element
            // examine new element in `found` and find it in indices
            let mut probe = entry.hash.desired_pos(Self::mask());

            probe_loop!(probe < self.indices.len(), {
                let pos: OptionalPos = self.indices[probe];
                if pos.is_some() {
                    if pos.index().unwrap() >= self.entries.len() {
                        // found it
                        // FIXME unwrap is actually unsafe for 0xffffffff
                        self.indices[probe] = OptionalPos::some(found, entry.hash).unwrap();
                        break;
                    }
                }
            });
        }

        self.backward_shift_after_removal(probe);

        (entry.key, entry.value)
    }

    fn backward_shift_after_removal(&mut self, probe_at_remove: usize) {
        // backward shift deletion in self.indices
        // after probe, shift all non-ideally placed indices backward
        let mut last_probe = probe_at_remove;
        let mut probe = probe_at_remove + 1;

        probe_loop!(probe < self.indices.len(), {
            let pos = self.indices[probe];
            if pos.is_some() {
                let entry_hash = pos.hash().unwrap();

                if entry_hash.probe_distance(Self::mask(), probe) > 0 {
                    unsafe { *self.indices.get_unchecked_mut(last_probe) = self.indices[probe] }
                    self.indices[probe] = OptionalPos::none();
                } else {
                    break;
                }
            } else {
                break;
            }
            last_probe = probe;
        });
    }
}

/// Fixed capacity [`IndexMap`](https://docs.rs/indexmap/1/indexmap/map/struct.IndexMap.html)
///
/// Note that the capacity of the `IndexMap` must be a power of 2.
///
/// # Examples
///
/// ```
/// use heapless::FnvIndexMap;
/// use heapless::consts::*;
///
/// // A hash map with a capacity of 16 key-value pairs allocated on the stack
/// let mut book_reviews = FnvIndexMap::<_, _, U16>::new();
///
/// // review some books.
/// book_reviews.insert("Adventures of Huckleberry Finn",    "My favorite book.").unwrap();
/// book_reviews.insert("Grimms' Fairy Tales",               "Masterpiece.").unwrap();
/// book_reviews.insert("Pride and Prejudice",               "Very enjoyable.").unwrap();
/// book_reviews.insert("The Adventures of Sherlock Holmes", "Eye lyked it alot.").unwrap();
///
/// // check for a specific one.
/// if !book_reviews.contains_key("Les Misérables") {
///     println!("We've got {} reviews, but Les Misérables ain't one.",
///              book_reviews.len());
/// }
///
/// // oops, this review has a lot of spelling mistakes, let's delete it.
/// book_reviews.remove("The Adventures of Sherlock Holmes");
///
/// // look up the values associated with some keys.
/// let to_find = ["Pride and Prejudice", "Alice's Adventure in Wonderland"];
/// for book in &to_find {
///     match book_reviews.get(book) {
///         Some(review) => println!("{}: {}", book, review),
///         None => println!("{} is unreviewed.", book)
///     }
/// }
///
/// // iterate over everything.
/// for (book, review) in &book_reviews {
///     println!("{}: \"{}\"", book, review);
/// }
/// ```
pub struct IndexMap<K, V, N, S>
where
    K: Eq + Hash,
    N: ArrayLength<Bucket<K, V>> + ArrayLength<OptionalPos>,
{
    core: CoreMap<K, V, N>,
    build_hasher: S,
}

impl<K, V, N, S> IndexMap<K, V, N, BuildHasherDefault<S>>
where
    K: Eq + Hash,
    S: Default + Hasher,
    N: ArrayLength<Bucket<K, V>> + ArrayLength<OptionalPos> + PowerOfTwo,
{
    // TODO turn into a `const fn`; needs `mem::zeroed` to be a `const fn`
    /// Creates an empty `IndexMap`.
    ///
    /// **NOTE** This constructor will become a `const fn` in the future
    pub fn new() -> Self {
        IndexMap {
            build_hasher: BuildHasherDefault::default(),
            core: CoreMap::new(),
        }
    }
}

impl<K, V, N, S> IndexMap<K, V, N, S>
where
    K: Eq + Hash,
    S: BuildHasher,
    N: ArrayLength<Bucket<K, V>> + ArrayLength<OptionalPos>,
{
    /* Public API */
    /// Returns the number of elements the map can hold
    pub fn capacity(&self) -> usize {
        N::to_usize()
    }

    /// Return an iterator over the keys of the map, in their order
    ///
    /// ```
    /// use heapless::FnvIndexMap;
    /// use heapless::consts::*;
    ///
    /// let mut map = FnvIndexMap::<_, _, U16>::new();
    /// map.insert("a", 1).unwrap();
    /// map.insert("b", 2).unwrap();
    /// map.insert("c", 3).unwrap();
    ///
    /// for key in map.keys() {
    ///     println!("{}", key);
    /// }
    /// ```
    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.core.entries.iter().map(|bucket| &bucket.key)
    }

    /// Return an iterator over the values of the map, in their order
    ///
    /// ```
    /// use heapless::FnvIndexMap;
    /// use heapless::consts::*;
    ///
    /// let mut map = FnvIndexMap::<_, _, U16>::new();
    /// map.insert("a", 1).unwrap();
    /// map.insert("b", 2).unwrap();
    /// map.insert("c", 3).unwrap();
    ///
    /// for val in map.values() {
    ///     println!("{}", val);
    /// }
    /// ```
    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.core.entries.iter().map(|bucket| &bucket.value)
    }

    /// Return an iterator over mutable references to the the values of the map, in their order
    ///
    /// ```
    /// use heapless::FnvIndexMap;
    /// use heapless::consts::*;
    ///
    /// let mut map = FnvIndexMap::<_, _, U16>::new();
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
        self.core.entries.iter_mut().map(|bucket| &mut bucket.value)
    }

    /// Return an iterator over the key-value pairs of the map, in their order
    ///
    /// ```
    /// use heapless::FnvIndexMap;
    /// use heapless::consts::*;
    ///
    /// let mut map = FnvIndexMap::<_, _, U16>::new();
    /// map.insert("a", 1).unwrap();
    /// map.insert("b", 2).unwrap();
    /// map.insert("c", 3).unwrap();
    ///
    /// for (key, val) in map.iter() {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            iter: self.core.entries.iter(),
        }
    }

    /// Return an iterator over the key-value pairs of the map, in their order
    ///
    /// ```
    /// use heapless::FnvIndexMap;
    /// use heapless::consts::*;
    ///
    /// let mut map = FnvIndexMap::<_, _, U16>::new();
    /// map.insert("a", 1).unwrap();
    /// map.insert("b", 2).unwrap();
    /// map.insert("c", 3).unwrap();
    ///
    /// for (_, val) in map.iter_mut() {
    ///     *val = 2;
    /// }
    ///
    /// for (key, val) in &map {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut {
            iter: self.core.entries.iter_mut(),
        }
    }

    // TODO
    // pub fn entry(&mut self, key: K) -> Entry<K, V> { .. }

    /// Return the number of key-value pairs in the map.
    ///
    /// Computes in **O(1)** time.
    ///
    /// ```
    /// use heapless::FnvIndexMap;
    /// use heapless::consts::*;
    ///
    /// let mut a = FnvIndexMap::<_, _, U16>::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(1, "a").unwrap();
    /// assert_eq!(a.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.core.entries.len()
    }

    /// Returns true if the map contains no elements.
    ///
    /// Computes in **O(1)** time.
    ///
    /// ```
    /// use heapless::FnvIndexMap;
    /// use heapless::consts::*;
    ///
    /// let mut a = FnvIndexMap::<_, _, U16>::new();
    /// assert!(a.is_empty());
    /// a.insert(1, "a");
    /// assert!(!a.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Remove all key-value pairs in the map, while preserving its capacity.
    ///
    /// Computes in **O(n)** time.
    ///
    /// ```
    /// use heapless::FnvIndexMap;
    /// use heapless::consts::*;
    ///
    /// let mut a = FnvIndexMap::<_, _, U16>::new();
    /// a.insert(1, "a");
    /// a.clear();
    /// assert!(a.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.core.entries.clear();
        for pos in self.core.indices.iter_mut() {
            *pos = OptionalPos::none();
        }
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but `Hash` and `Eq` on the borrowed
    /// form *must* match those for the key type.
    ///
    /// Computes in **O(1)** time (average).
    ///
    /// ```
    /// use heapless::FnvIndexMap;
    /// use heapless::consts::*;
    ///
    /// let mut map = FnvIndexMap::<_, _, U16>::new();
    /// map.insert(1, "a").unwrap();
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: ?Sized + Hash + Eq,
    {
        self.find(key)
            .map(|(_, found)| unsafe { &self.core.entries.get_unchecked(found).value })
    }

    /// Returns true if the map contains a value for the specified key.
    ///
    /// The key may be any borrowed form of the map's key type, but `Hash` and `Eq` on the borrowed
    /// form *must* match those for the key type.
    ///
    /// Computes in **O(1)** time (average).
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::FnvIndexMap;
    /// use heapless::consts::*;
    ///
    /// let mut map = FnvIndexMap::<_, _, U8>::new();
    /// map.insert(1, "a").unwrap();
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: ?Sized + Eq + Hash,
    {
        self.find(key).is_some()
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but `Hash` and `Eq` on the borrowed
    /// form *must* match those for the key type.
    ///
    /// Computes in **O(1)** time (average).
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::FnvIndexMap;
    /// use heapless::consts::*;
    ///
    /// let mut map = FnvIndexMap::<_, _, U8>::new();
    /// map.insert(1, "a").unwrap();
    /// if let Some(x) = map.get_mut(&1) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map[&1], "b");
    /// ```
    pub fn get_mut<'v, Q>(&'v mut self, key: &Q) -> Option<&'v mut V>
    where
        K: Borrow<Q>,
        Q: ?Sized + Hash + Eq,
    {
        if let Some((_, found)) = self.find(key) {
            Some(unsafe { &mut self.core.entries.get_unchecked_mut(found).value })
        } else {
            None
        }
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If an equivalent key already exists in the map: the key remains and retains in its place in
    /// the order, its corresponding value is updated with `value` and the older value is returned
    /// inside `Some(_)`.
    ///
    /// If no equivalent key existed in the map: the new key-value pair is inserted, last in order,
    /// and `None` is returned.
    ///
    /// Computes in **O(1)** time (average).
    ///
    /// See also entry if you you want to insert or modify or if you need to get the index of the
    /// corresponding key-value pair.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::FnvIndexMap;
    /// use heapless::consts::*;
    ///
    /// let mut map = FnvIndexMap::<_, _, U8>::new();
    /// assert_eq!(map.insert(37, "a"), Ok(None));
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(37, "b");
    /// assert_eq!(map.insert(37, "c"), Ok(Some("b")));
    /// assert_eq!(map[&37], "c");
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Result<Option<V>, (K, V)> {
        if self.core.entries.is_full() {
            Err((key, value))
        } else {
            Ok(match self.insert_phase_1(key, value) {
                Inserted::Swapped { prev_value } => Some(prev_value),
                Inserted::Done => None,
                Inserted::RobinHood { probe, old_pos } => {
                    self.core.insert_phase_2(probe, old_pos);
                    None
                }
            })
        }
    }

    /// Same as [`swap_remove`](struct.IndexMap.html#method.swap_remove)
    ///
    /// Computes in **O(1)** time (average).
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::FnvIndexMap;
    /// use heapless::consts::*;
    ///
    /// let mut map = FnvIndexMap::<_, _, U8>::new();
    /// map.insert(1, "a").unwrap();
    /// assert_eq!(map.remove(&1), Some("a"));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: ?Sized + Hash + Eq,
    {
        self.swap_remove(key)
    }

    /// Remove the key-value pair equivalent to `key` and return its value.
    ///
    /// Like `Vec::swap_remove`, the pair is removed by swapping it with the last element of the map
    /// and popping it off. **This perturbs the postion of what used to be the last element!**
    ///
    /// Return `None` if `key` is not in map.
    ///
    /// Computes in **O(1)** time (average).
    pub fn swap_remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: ?Sized + Hash + Eq,
    {
        self.find(key)
            .map(|(probe, found)| self.core.remove_found(probe, found).1)
    }

    /* Private API */
    /// Return probe (indices) and position (entries)
    fn find<Q>(&self, key: &Q) -> Option<(usize, usize)>
    where
        K: Borrow<Q>,
        Q: ?Sized + Hash + Eq,
    {
        if self.len() == 0 {
            return None;
        }
        let h = hash_with(key, &self.build_hasher);
        self.core.find(h, key)
    }

    fn insert_phase_1(&mut self, key: K, value: V) -> Inserted<V> {
        let hash = hash_with(&key, &self.build_hasher);
        self.core.insert_phase_1(hash, key, value)
    }
}

impl<'a, K, Q, V, N, S> ops::Index<&'a Q> for IndexMap<K, V, N, S>
where
    K: Eq + Hash + Borrow<Q>,
    Q: ?Sized + Eq + Hash,
    S: BuildHasher,
    N: ArrayLength<Bucket<K, V>> + ArrayLength<OptionalPos>,
{
    type Output = V;

    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("key not found")
    }
}

impl<'a, K, Q, V, N, S> ops::IndexMut<&'a Q> for IndexMap<K, V, N, S>
where
    K: Eq + Hash + Borrow<Q>,
    Q: ?Sized + Eq + Hash,
    S: BuildHasher,
    N: ArrayLength<Bucket<K, V>> + ArrayLength<OptionalPos>,
{
    fn index_mut(&mut self, key: &Q) -> &mut V {
        self.get_mut(key).expect("key not found")
    }
}

impl<K, V, N, S> fmt::Debug for IndexMap<K, V, N, S>
where
    K: Eq + Hash + fmt::Debug,
    V: fmt::Debug,
    S: BuildHasher,
    N: ArrayLength<Bucket<K, V>> + ArrayLength<OptionalPos>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, V, N, S> Default for IndexMap<K, V, N, S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
    N: ArrayLength<Bucket<K, V>> + ArrayLength<OptionalPos>,
{
    fn default() -> Self {
        IndexMap {
            build_hasher: <_>::default(),
            core: CoreMap::new(),
        }
    }
}

impl<K, V, N, S> Extend<(K, V)> for IndexMap<K, V, N, S>
where
    K: Eq + Hash,
    S: BuildHasher,
    N: ArrayLength<Bucket<K, V>> + ArrayLength<OptionalPos>,
{
    fn extend<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = (K, V)>,
    {
        for (k, v) in iterable {
            self.insert(k, v).ok().unwrap();
        }
    }
}

impl<'a, K, V, N, S> Extend<(&'a K, &'a V)> for IndexMap<K, V, N, S>
where
    K: Eq + Hash + Copy,
    V: Copy,
    S: BuildHasher,
    N: ArrayLength<Bucket<K, V>> + ArrayLength<OptionalPos>,
{
    fn extend<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = (&'a K, &'a V)>,
    {
        self.extend(iterable.into_iter().map(|(&key, &value)| (key, value)))
    }
}

impl<K, V, N, S> FromIterator<(K, V)> for IndexMap<K, V, N, S>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
    N: ArrayLength<Bucket<K, V>> + ArrayLength<OptionalPos>,
{
    fn from_iter<I>(iterable: I) -> Self
    where
        I: IntoIterator<Item = (K, V)>,
    {
        let mut map = IndexMap::default();
        map.extend(iterable);
        map
    }
}

impl<'a, K, V, N, S> IntoIterator for &'a IndexMap<K, V, N, S>
where
    K: Eq + Hash,
    S: BuildHasher,
    N: ArrayLength<Bucket<K, V>> + ArrayLength<OptionalPos>,
{
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, V, N, S> IntoIterator for &'a mut IndexMap<K, V, N, S>
where
    K: Eq + Hash,
    S: BuildHasher,
    N: ArrayLength<Bucket<K, V>> + ArrayLength<OptionalPos>,
{
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

pub struct Iter<'a, K, V>
where
    K: 'a,
    V: 'a,
{
    iter: slice::Iter<'a, Bucket<K, V>>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V>
where
    K: 'a,
    V: 'a,
{
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|bucket| (&bucket.key, &bucket.value))
    }
}

pub struct IterMut<'a, K, V>
where
    K: 'a,
    V: 'a,
{
    iter: slice::IterMut<'a, Bucket<K, V>>,
}

impl<'a, K, V> Iterator for IterMut<'a, K, V>
where
    K: 'a,
    V: 'a,
{
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()
            .map(|bucket| (&bucket.key, &mut bucket.value))
    }
}

fn hash_with<K, S>(key: &K, build_hasher: &S) -> HashValue
where
    K: ?Sized + Hash,
    S: BuildHasher,
{
    let mut h = build_hasher.build_hasher();
    key.hash(&mut h);
    HashValue(h.finish() as u16)
}

#[cfg(test)]
mod tests {
    use core::mem;

    use generic_array::typenum::Unsigned;

    use consts::*;
    use FnvIndexMap;

    #[test]
    fn size() {
        type Cap = U4;

        let cap = Cap::to_usize();
        assert_eq!(
            mem::size_of::<FnvIndexMap<i16, u16, Cap>>(),
            cap * mem::size_of::<u32>() + // indices
                cap * (mem::size_of::<i16>() + // key
                     mem::size_of::<u16>() + // value
                     mem::size_of::<u16>() // hash
                ) + // buckets
                mem::size_of::<usize>() // entries.length
        )
    }
}

use core::{
    borrow::Borrow,
    fmt,
    hash::{BuildHasher, Hash, Hasher as _},
    iter::FromIterator,
    mem,
    num::NonZeroU32,
    ops, slice,
};

use hash32::{BuildHasherDefault, FnvHasher};

use crate::Vec;

/// A [`heapless::IndexMap`](./struct.IndexMap.html) using the default FNV hasher
///
/// A list of all Methods and Traits available for `FnvIndexMap` can be found in
/// the [`heapless::IndexMap`](./struct.IndexMap.html) documentation.
///
/// # Examples
/// ```
/// use heapless::FnvIndexMap;
///
/// // A hash map with a capacity of 16 key-value pairs allocated on the stack
/// let mut book_reviews = FnvIndexMap::<_, _, 16>::new();
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
pub type FnvIndexMap<K, V, const N: usize> = IndexMap<K, V, BuildHasherDefault<FnvHasher>, N>;

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
#[derive(Clone)]
pub struct Bucket<K, V> {
    hash: HashValue,
    key: K,
    value: V,
}

#[doc(hidden)]
#[derive(Clone, Copy, PartialEq)]
pub struct Pos {
    // compact representation of `{ hash_value: u16, index: u16 }`
    // To get the most from `NonZero` we store the *value minus 1*. This way `None::Option<Pos>`
    // is equivalent to the very unlikely value of  `{ hash_value: 0xffff, index: 0xffff }` instead
    // the more likely of `{ hash_value: 0x00, index: 0x00 }`
    nz: NonZeroU32,
}

impl Pos {
    fn new(index: usize, hash: HashValue) -> Self {
        Pos {
            nz: unsafe {
                NonZeroU32::new_unchecked(
                    ((u32::from(hash.0) << 16) + index as u32).wrapping_add(1),
                )
            },
        }
    }

    fn hash(&self) -> HashValue {
        HashValue((self.nz.get().wrapping_sub(1) >> 16) as u16)
    }

    fn index(&self) -> usize {
        self.nz.get().wrapping_sub(1) as u16 as usize
    }
}

enum Insert<K, V> {
    Success(Inserted<V>),
    Full((K, V)),
}
struct Inserted<V> {
    index: usize,
    old_value: Option<V>,
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

struct CoreMap<K, V, const N: usize> {
    entries: Vec<Bucket<K, V>, N>,
    indices: [Option<Pos>; N],
}

impl<K, V, const N: usize> CoreMap<K, V, N> {
    const fn new() -> Self {
        const INIT: Option<Pos> = None;

        CoreMap {
            entries: Vec::new(),
            indices: [INIT; N],
        }
    }
}

impl<K, V, const N: usize> CoreMap<K, V, N>
where
    K: Eq + Hash,
{
    fn capacity() -> usize {
        N
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
            if let Some(pos) = self.indices[probe] {
                let entry_hash = pos.hash();
                // NOTE(i) we use unchecked indexing below
                let i = pos.index();
                debug_assert!(i < self.entries.len());

                if dist > entry_hash.probe_distance(Self::mask(), probe) {
                    // give up when probe distance is too long
                    return None;
                } else if entry_hash == hash
                    && unsafe { self.entries.get_unchecked(i).key.borrow() == query }
                {
                    return Some((probe, i));
                }
            } else {
                return None;
            }

            dist += 1;
        });
    }

    fn insert(&mut self, hash: HashValue, key: K, value: V) -> Insert<K, V> {
        let mut probe = hash.desired_pos(Self::mask());
        let mut dist = 0;

        probe_loop!(probe < self.indices.len(), {
            let pos = &mut self.indices[probe];

            if let Some(pos) = *pos {
                let entry_hash = pos.hash();
                // NOTE(i) we use unchecked indexing below
                let i = pos.index();
                debug_assert!(i < self.entries.len());

                let their_dist = entry_hash.probe_distance(Self::mask(), probe);

                if their_dist < dist {
                    if self.entries.is_full() {
                        return Insert::Full((key, value));
                    }
                    // robin hood: steal the spot if it's better for us
                    let index = self.entries.len();
                    unsafe { self.entries.push_unchecked(Bucket { hash, key, value }) };
                    Self::insert_phase_2(&mut self.indices, probe, Pos::new(index, hash));
                    return Insert::Success(Inserted {
                        index,
                        old_value: None,
                    });
                } else if entry_hash == hash && unsafe { self.entries.get_unchecked(i).key == key }
                {
                    return Insert::Success(Inserted {
                        index: i,
                        old_value: Some(mem::replace(
                            unsafe { &mut self.entries.get_unchecked_mut(i).value },
                            value,
                        )),
                    });
                }
            } else {
                if self.entries.is_full() {
                    return Insert::Full((key, value));
                }
                // empty bucket, insert here
                let index = self.entries.len();
                *pos = Some(Pos::new(index, hash));
                unsafe { self.entries.push_unchecked(Bucket { hash, key, value }) };
                return Insert::Success(Inserted {
                    index,
                    old_value: None,
                });
            }
            dist += 1;
        });
    }

    // phase 2 is post-insert where we forward-shift `Pos` in the indices.
    fn insert_phase_2(indices: &mut [Option<Pos>; N], mut probe: usize, mut old_pos: Pos) -> usize {
        probe_loop!(probe < indices.len(), {
            let pos = unsafe { indices.get_unchecked_mut(probe) };

            let mut is_none = true; // work around lack of NLL
            if let Some(pos) = pos.as_mut() {
                old_pos = mem::replace(pos, old_pos);
                is_none = false;
            }

            if is_none {
                *pos = Some(old_pos);
                return probe;
            }
        });
    }

    fn remove_found(&mut self, probe: usize, found: usize) -> (K, V) {
        // index `probe` and entry `found` is to be removed
        // use swap_remove, but then we need to update the index that points
        // to the other entry that has to move
        self.indices[probe] = None;
        let entry = unsafe { self.entries.swap_remove_unchecked(found) };

        // correct index that points to the entry that had to swap places
        if let Some(entry) = self.entries.get(found) {
            // was not last element
            // examine new element in `found` and find it in indices
            let mut probe = entry.hash.desired_pos(Self::mask());

            probe_loop!(probe < self.indices.len(), {
                if let Some(pos) = self.indices[probe] {
                    if pos.index() >= self.entries.len() {
                        // found it
                        self.indices[probe] = Some(Pos::new(found, entry.hash));
                        break;
                    }
                }
            });
        }

        self.backward_shift_after_removal(probe);

        (entry.key, entry.value)
    }

    fn retain_in_order<F>(&mut self, mut keep: F)
    where
        F: FnMut(&mut K, &mut V) -> bool,
    {
        const INIT: Option<Pos> = None;

        self.entries
            .retain_mut(|entry| keep(&mut entry.key, &mut entry.value));

        if self.entries.len() < self.indices.len() {
            for index in self.indices.iter_mut() {
                *index = INIT;
            }

            for (index, entry) in self.entries.iter().enumerate() {
                let mut probe = entry.hash.desired_pos(Self::mask());
                let mut dist = 0;

                probe_loop!(probe < self.indices.len(), {
                    let pos = &mut self.indices[probe];

                    if let Some(pos) = *pos {
                        let entry_hash = pos.hash();

                        // robin hood: steal the spot if it's better for us
                        let their_dist = entry_hash.probe_distance(Self::mask(), probe);
                        if their_dist < dist {
                            Self::insert_phase_2(
                                &mut self.indices,
                                probe,
                                Pos::new(index, entry.hash),
                            );
                            break;
                        }
                    } else {
                        *pos = Some(Pos::new(index, entry.hash));
                        break;
                    }
                    dist += 1;
                });
            }
        }
    }

    fn backward_shift_after_removal(&mut self, probe_at_remove: usize) {
        // backward shift deletion in self.indices
        // after probe, shift all non-ideally placed indices backward
        let mut last_probe = probe_at_remove;
        let mut probe = probe_at_remove + 1;

        probe_loop!(probe < self.indices.len(), {
            if let Some(pos) = self.indices[probe] {
                let entry_hash = pos.hash();

                if entry_hash.probe_distance(Self::mask(), probe) > 0 {
                    unsafe { *self.indices.get_unchecked_mut(last_probe) = self.indices[probe] }
                    self.indices[probe] = None;
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

impl<K, V, const N: usize> Clone for CoreMap<K, V, N>
where
    K: Clone,
    V: Clone,
{
    fn clone(&self) -> Self {
        Self {
            entries: self.entries.clone(),
            indices: self.indices.clone(),
        }
    }
}

/// A view into an entry in the map
pub enum Entry<'a, K, V, const N: usize> {
    /// The entry corresponding to the key `K` exists in the map
    Occupied(OccupiedEntry<'a, K, V, N>),
    /// The entry corresponding to the key `K` does not exist in the map
    Vacant(VacantEntry<'a, K, V, N>),
}

/// An occupied entry which can be manipulated
pub struct OccupiedEntry<'a, K, V, const N: usize> {
    key: K,
    probe: usize,
    pos: usize,
    core: &'a mut CoreMap<K, V, N>,
}

impl<'a, K, V, const N: usize> OccupiedEntry<'a, K, V, N>
where
    K: Eq + Hash,
{
    /// Gets a reference to the key that this entity corresponds to
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Removes this entry from the map and yields its corresponding key and value
    pub fn remove_entry(self) -> (K, V) {
        self.core.remove_found(self.probe, self.pos)
    }

    /// Gets a reference to the value associated with this entry
    pub fn get(&self) -> &V {
        // SAFETY: Already checked existence at instantiation and the only mutable reference
        // to the map is internally held.
        unsafe { &self.core.entries.get_unchecked(self.pos).value }
    }

    /// Gets a mutable reference to the value associated with this entry
    pub fn get_mut(&mut self) -> &mut V {
        // SAFETY: Already checked existence at instantiation and the only mutable reference
        // to the map is internally held.
        unsafe { &mut self.core.entries.get_unchecked_mut(self.pos).value }
    }

    /// Consumes this entry and yields a reference to the underlying value
    pub fn into_mut(self) -> &'a mut V {
        // SAFETY: Already checked existence at instantiation and the only mutable reference
        // to the map is internally held.
        unsafe { &mut self.core.entries.get_unchecked_mut(self.pos).value }
    }

    /// Overwrites the underlying map's value with this entry's value
    pub fn insert(self, value: V) -> V {
        // SAFETY: Already checked existence at instantiation and the only mutable reference
        // to the map is internally held.
        unsafe {
            mem::replace(
                &mut self.core.entries.get_unchecked_mut(self.pos).value,
                value,
            )
        }
    }

    /// Removes this entry from the map and yields its value
    pub fn remove(self) -> V {
        self.remove_entry().1
    }
}

/// A view into an empty slot in the underlying map
pub struct VacantEntry<'a, K, V, const N: usize> {
    key: K,
    hash_val: HashValue,
    core: &'a mut CoreMap<K, V, N>,
}
impl<'a, K, V, const N: usize> VacantEntry<'a, K, V, N>
where
    K: Eq + Hash,
{
    /// Get the key associated with this entry
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Consumes this entry to yield to key associated with it
    pub fn into_key(self) -> K {
        self.key
    }

    /// Inserts this entry into to underlying map, yields a mutable reference to the inserted value.
    /// If the map is at capacity the value is returned instead.
    pub fn insert(self, value: V) -> Result<&'a mut V, V> {
        if self.core.entries.is_full() {
            Err(value)
        } else {
            match self.core.insert(self.hash_val, self.key, value) {
                Insert::Success(inserted) => {
                    unsafe {
                        // SAFETY: Already checked existence at instantiation and the only mutable reference
                        // to the map is internally held.
                        Ok(&mut (*self.core.entries.as_mut_ptr().add(inserted.index)).value)
                    }
                }
                Insert::Full((_, v)) => Err(v),
            }
        }
    }
}

/// Fixed capacity [`IndexMap`](https://docs.rs/indexmap/1/indexmap/map/struct.IndexMap.html)
///
/// Note that you cannot use `IndexMap` directly, since it is generic around the hashing algorithm
/// in use. Pick a concrete instantiation like [`FnvIndexMap`](./type.FnvIndexMap.html) instead
/// or create your own.
///
/// Note that the capacity of the `IndexMap` must be a power of 2.
///
/// # Examples
/// Since `IndexMap` cannot be used directly, we're using its `FnvIndexMap` instantiation
/// for this example.
///
/// ```
/// use heapless::FnvIndexMap;
///
/// // A hash map with a capacity of 16 key-value pairs allocated on the stack
/// let mut book_reviews = FnvIndexMap::<_, _, 16>::new();
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
pub struct IndexMap<K, V, S, const N: usize> {
    core: CoreMap<K, V, N>,
    build_hasher: S,
}

impl<K, V, S, const N: usize> IndexMap<K, V, BuildHasherDefault<S>, N> {
    /// Creates an empty `IndexMap`.
    pub const fn new() -> Self {
        // Const assert
        crate::sealed::greater_than_1::<N>();
        crate::sealed::power_of_two::<N>();

        IndexMap {
            build_hasher: BuildHasherDefault::new(),
            core: CoreMap::new(),
        }
    }
}

impl<K, V, S, const N: usize> IndexMap<K, V, S, N> {
    /// Returns the number of elements the map can hold
    pub fn capacity(&self) -> usize {
        N
    }

    /// Return an iterator over the keys of the map, in insertion order
    ///
    /// ```
    /// use heapless::FnvIndexMap;
    ///
    /// let mut map = FnvIndexMap::<_, _, 16>::new();
    /// map.insert("a", 1).unwrap();
    /// map.insert("b", 2).unwrap();
    /// map.insert("c", 3).unwrap();
    ///
    /// for key in map.keys() {
    ///     println!("{}", key);
    /// }
    /// ```
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys {
            iter: self.core.entries.iter(),
        }
    }

    /// Return an iterator over the values of the map, in insertion order
    ///
    /// ```
    /// use heapless::FnvIndexMap;
    ///
    /// let mut map = FnvIndexMap::<_, _, 16>::new();
    /// map.insert("a", 1).unwrap();
    /// map.insert("b", 2).unwrap();
    /// map.insert("c", 3).unwrap();
    ///
    /// for val in map.values() {
    ///     println!("{}", val);
    /// }
    /// ```
    pub fn values(&self) -> Values<'_, K, V> {
        Values {
            iter: self.core.entries.iter(),
        }
    }

    /// Return an iterator over mutable references to the the values of the map, in insertion order
    ///
    /// ```
    /// use heapless::FnvIndexMap;
    ///
    /// let mut map = FnvIndexMap::<_, _, 16>::new();
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
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut {
            iter: self.core.entries.iter_mut(),
        }
    }

    /// Return an iterator over the key-value pairs of the map, in insertion order
    ///
    /// ```
    /// use heapless::FnvIndexMap;
    ///
    /// let mut map = FnvIndexMap::<_, _, 16>::new();
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
            iter: self.core.entries.iter(),
        }
    }

    /// Return an iterator over the key-value pairs of the map, in insertion order
    ///
    /// ```
    /// use heapless::FnvIndexMap;
    ///
    /// let mut map = FnvIndexMap::<_, _, 16>::new();
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
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut {
            iter: self.core.entries.iter_mut(),
        }
    }

    /// Get the first key-value pair
    ///
    /// Computes in **O(1)** time
    pub fn first(&self) -> Option<(&K, &V)> {
        self.core
            .entries
            .first()
            .map(|bucket| (&bucket.key, &bucket.value))
    }

    /// Get the first key-value pair, with mutable access to the value
    ///
    /// Computes in **O(1)** time
    pub fn first_mut(&mut self) -> Option<(&K, &mut V)> {
        self.core
            .entries
            .first_mut()
            .map(|bucket| (&bucket.key, &mut bucket.value))
    }

    /// Get the last key-value pair
    ///
    /// Computes in **O(1)** time
    pub fn last(&self) -> Option<(&K, &V)> {
        self.core
            .entries
            .last()
            .map(|bucket| (&bucket.key, &bucket.value))
    }

    /// Get the last key-value pair, with mutable access to the value
    ///
    /// Computes in **O(1)** time
    pub fn last_mut(&mut self) -> Option<(&K, &mut V)> {
        self.core
            .entries
            .last_mut()
            .map(|bucket| (&bucket.key, &mut bucket.value))
    }

    /// Return the number of key-value pairs in the map.
    ///
    /// Computes in **O(1)** time.
    ///
    /// ```
    /// use heapless::FnvIndexMap;
    ///
    /// let mut a = FnvIndexMap::<_, _, 16>::new();
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
    ///
    /// let mut a = FnvIndexMap::<_, _, 16>::new();
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
    ///
    /// let mut a = FnvIndexMap::<_, _, 16>::new();
    /// a.insert(1, "a");
    /// a.clear();
    /// assert!(a.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.core.entries.clear();
        for pos in self.core.indices.iter_mut() {
            *pos = None;
        }
    }
}

impl<K, V, S, const N: usize> IndexMap<K, V, S, N>
where
    K: Eq + Hash,
    S: BuildHasher,
{
    /* Public API */
    /// Returns an entry for the corresponding key
    /// ```
    /// use heapless::FnvIndexMap;
    /// use heapless::Entry;
    /// let mut map = FnvIndexMap::<_, _, 16>::new();
    /// if let Entry::Vacant(v) = map.entry("a") {
    ///     v.insert(1).unwrap();
    /// }
    /// if let Entry::Occupied(mut o) = map.entry("a") {
    ///     println!("found {}", *o.get()); // Prints 1
    ///     o.insert(2);
    /// }
    /// // Prints 2
    /// println!("val: {}", *map.get("a").unwrap());
    /// ```
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V, N> {
        let hash_val = hash_with(&key, &self.build_hasher);
        if let Some((probe, pos)) = self.core.find(hash_val, &key) {
            Entry::Occupied(OccupiedEntry {
                key,
                probe,
                pos,
                core: &mut self.core,
            })
        } else {
            Entry::Vacant(VacantEntry {
                key,
                hash_val,
                core: &mut self.core,
            })
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
    ///
    /// let mut map = FnvIndexMap::<_, _, 16>::new();
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
    ///
    /// let mut map = FnvIndexMap::<_, _, 8>::new();
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
    ///
    /// let mut map = FnvIndexMap::<_, _, 8>::new();
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
    ///
    /// let mut map = FnvIndexMap::<_, _, 8>::new();
    /// assert_eq!(map.insert(37, "a"), Ok(None));
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(37, "b");
    /// assert_eq!(map.insert(37, "c"), Ok(Some("b")));
    /// assert_eq!(map[&37], "c");
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Result<Option<V>, (K, V)> {
        let hash = hash_with(&key, &self.build_hasher);
        match self.core.insert(hash, key, value) {
            Insert::Success(inserted) => Ok(inserted.old_value),
            Insert::Full((k, v)) => Err((k, v)),
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
    ///
    /// let mut map = FnvIndexMap::<_, _, 8>::new();
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

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all pairs `(k, v)` for which `f(&k, &mut v)` returns `false`.
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        self.core.retain_in_order(move |k, v| f(k, v));
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
}

impl<'a, K, Q, V, S, const N: usize> ops::Index<&'a Q> for IndexMap<K, V, S, N>
where
    K: Eq + Hash + Borrow<Q>,
    Q: ?Sized + Eq + Hash,
    S: BuildHasher,
{
    type Output = V;

    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("key not found")
    }
}

impl<'a, K, Q, V, S, const N: usize> ops::IndexMut<&'a Q> for IndexMap<K, V, S, N>
where
    K: Eq + Hash + Borrow<Q>,
    Q: ?Sized + Eq + Hash,
    S: BuildHasher,
{
    fn index_mut(&mut self, key: &Q) -> &mut V {
        self.get_mut(key).expect("key not found")
    }
}

impl<K, V, S, const N: usize> Clone for IndexMap<K, V, S, N>
where
    K: Clone,
    V: Clone,
    S: Clone,
{
    fn clone(&self) -> Self {
        Self {
            core: self.core.clone(),
            build_hasher: self.build_hasher.clone(),
        }
    }
}

impl<K, V, S, const N: usize> fmt::Debug for IndexMap<K, V, S, N>
where
    K: fmt::Debug,
    V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K, V, S, const N: usize> Default for IndexMap<K, V, S, N>
where
    S: Default,
{
    fn default() -> Self {
        // Const assert
        crate::sealed::greater_than_1::<N>();
        crate::sealed::power_of_two::<N>();

        IndexMap {
            build_hasher: <_>::default(),
            core: CoreMap::new(),
        }
    }
}

impl<K, V, S, S2, const N: usize, const N2: usize> PartialEq<IndexMap<K, V, S2, N2>>
    for IndexMap<K, V, S, N>
where
    K: Eq + Hash,
    V: Eq,
    S: BuildHasher,
    S2: BuildHasher,
{
    fn eq(&self, other: &IndexMap<K, V, S2, N2>) -> bool {
        self.len() == other.len()
            && self
                .iter()
                .all(|(key, value)| other.get(key).map_or(false, |v| *value == *v))
    }
}

impl<K, V, S, const N: usize> Eq for IndexMap<K, V, S, N>
where
    K: Eq + Hash,
    V: Eq,
    S: BuildHasher,
{
}

impl<K, V, S, const N: usize> Extend<(K, V)> for IndexMap<K, V, S, N>
where
    K: Eq + Hash,
    S: BuildHasher,
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

impl<'a, K, V, S, const N: usize> Extend<(&'a K, &'a V)> for IndexMap<K, V, S, N>
where
    K: Eq + Hash + Copy,
    V: Copy,
    S: BuildHasher,
{
    fn extend<I>(&mut self, iterable: I)
    where
        I: IntoIterator<Item = (&'a K, &'a V)>,
    {
        self.extend(iterable.into_iter().map(|(&key, &value)| (key, value)))
    }
}

impl<K, V, S, const N: usize> FromIterator<(K, V)> for IndexMap<K, V, S, N>
where
    K: Eq + Hash,
    S: BuildHasher + Default,
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

#[derive(Clone)]
pub struct IntoIter<K, V, const N: usize> {
    entries: Vec<Bucket<K, V>, N>,
}

impl<K, V, const N: usize> Iterator for IntoIter<K, V, N> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.entries.pop().map(|bucket| (bucket.key, bucket.value))
    }
}

impl<K, V, S, const N: usize> IntoIterator for IndexMap<K, V, S, N> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V, N>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            entries: self.core.entries,
        }
    }
}

impl<'a, K, V, S, const N: usize> IntoIterator for &'a IndexMap<K, V, S, N> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, V, S, const N: usize> IntoIterator for &'a mut IndexMap<K, V, S, N> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

/// An iterator over the items of a [`IndexMap`].
///
/// This `struct` is created by the [`iter`](IndexMap::iter) method on [`IndexMap`]. See its
/// documentation for more.
pub struct Iter<'a, K, V> {
    iter: slice::Iter<'a, Bucket<K, V>>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|bucket| (&bucket.key, &bucket.value))
    }
}

impl<'a, K, V> Clone for Iter<'a, K, V> {
    fn clone(&self) -> Self {
        Self {
            iter: self.iter.clone(),
        }
    }
}

/// A mutable iterator over the items of a [`IndexMap`].
///
/// This `struct` is created by the [`iter_mut`](IndexMap::iter_mut) method on [`IndexMap`]. See its
/// documentation for more.
pub struct IterMut<'a, K, V> {
    iter: slice::IterMut<'a, Bucket<K, V>>,
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()
            .map(|bucket| (&bucket.key, &mut bucket.value))
    }
}

/// An iterator over the keys of a [`IndexMap`].
///
/// This `struct` is created by the [`keys`](IndexMap::keys) method on [`IndexMap`]. See its
/// documentation for more.
pub struct Keys<'a, K, V> {
    iter: slice::Iter<'a, Bucket<K, V>>,
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|bucket| &bucket.key)
    }
}

/// An iterator over the values of a [`IndexMap`].
///
/// This `struct` is created by the [`values`](IndexMap::values) method on [`IndexMap`]. See its
/// documentation for more.
pub struct Values<'a, K, V> {
    iter: slice::Iter<'a, Bucket<K, V>>,
}

impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|bucket| &bucket.value)
    }
}

/// A mutable iterator over the values of a [`IndexMap`].
///
/// This `struct` is created by the [`values_mut`](IndexMap::values_mut) method on [`IndexMap`]. See its
/// documentation for more.
pub struct ValuesMut<'a, K, V> {
    iter: slice::IterMut<'a, Bucket<K, V>>,
}

impl<'a, K, V> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|bucket| &mut bucket.value)
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
    use crate::{indexmap::Entry, FnvIndexMap};

    use core::mem;

    #[test]
    fn size() {
        const CAP: usize = 4;
        assert_eq!(
            mem::size_of::<FnvIndexMap<i16, u16, CAP>>(),
            CAP * mem::size_of::<u32>() + // indices
                CAP * (mem::size_of::<i16>() + // key
                     mem::size_of::<u16>() + // value
                     mem::size_of::<u16>() // hash
                ) + // buckets
                mem::size_of::<usize>() // entries.length
        )
    }

    #[test]
    fn partial_eq() {
        {
            let mut a: FnvIndexMap<_, _, 4> = FnvIndexMap::new();
            a.insert("k1", "v1").unwrap();

            let mut b: FnvIndexMap<_, _, 4> = FnvIndexMap::new();
            b.insert("k1", "v1").unwrap();

            assert!(a == b);

            b.insert("k2", "v2").unwrap();

            assert!(a != b);
        }

        {
            let mut a: FnvIndexMap<_, _, 4> = FnvIndexMap::new();
            a.insert("k1", "v1").unwrap();
            a.insert("k2", "v2").unwrap();

            let mut b: FnvIndexMap<_, _, 4> = FnvIndexMap::new();
            b.insert("k2", "v2").unwrap();
            b.insert("k1", "v1").unwrap();

            assert!(a == b);
        }
    }

    #[test]
    fn into_iter() {
        let mut src: FnvIndexMap<_, _, 4> = FnvIndexMap::new();
        src.insert("k1", "v1").unwrap();
        src.insert("k2", "v2").unwrap();
        src.insert("k3", "v3").unwrap();
        src.insert("k4", "v4").unwrap();
        let clone = src.clone();
        for (k, v) in clone.into_iter() {
            assert_eq!(v, *src.get(k).unwrap());
        }
    }

    #[test]
    fn insert_replaces_on_full_map() {
        let mut a: FnvIndexMap<_, _, 2> = FnvIndexMap::new();
        a.insert("k1", "v1").unwrap();
        a.insert("k2", "v2").unwrap();
        a.insert("k1", "v2").unwrap();
        assert_eq!(a.get("k1"), a.get("k2"));
    }

    // tests that use this constant take too long to run under miri, specially on CI, with a map of
    // this size so make the map smaller when using miri
    #[cfg(not(miri))]
    const MAP_SLOTS: usize = 4096;
    #[cfg(miri)]
    const MAP_SLOTS: usize = 64;
    fn almost_filled_map() -> FnvIndexMap<usize, usize, MAP_SLOTS> {
        let mut almost_filled = FnvIndexMap::new();
        for i in 1..MAP_SLOTS {
            almost_filled.insert(i, i).unwrap();
        }
        almost_filled
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
        assert_eq!(value, *src.get(&key).unwrap())
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
        assert_eq!(value2, *src.get(&key).unwrap())
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
    fn retain() {
        let mut none = almost_filled_map();
        none.retain(|_, _| false);
        assert!(none.is_empty());

        let mut all = almost_filled_map();
        all.retain(|_, _| true);
        assert_eq!(all.len(), MAP_SLOTS - 1);

        let mut even = almost_filled_map();
        even.retain(|_, &mut v| v % 2 == 0);
        assert_eq!(even.len(), (MAP_SLOTS - 1) / 2);
        for &v in even.values() {
            assert_eq!(v % 2, 0);
        }

        let mut odd = almost_filled_map();
        odd.retain(|_, &mut v| v % 2 != 0);
        assert_eq!(odd.len(), MAP_SLOTS / 2);
        for &v in odd.values() {
            assert_ne!(v % 2, 0);
        }
        assert_eq!(odd.insert(2, 2), Ok(None));
        assert_eq!(odd.len(), (MAP_SLOTS / 2) + 1);
    }

    #[test]
    fn entry_roll_through_all() {
        let mut src: FnvIndexMap<usize, usize, MAP_SLOTS> = FnvIndexMap::new();
        for i in 0..MAP_SLOTS {
            match src.entry(i) {
                Entry::Occupied(_) => {
                    panic!("Entry found before insert");
                }
                Entry::Vacant(v) => {
                    v.insert(i).unwrap();
                }
            }
        }
        let add_mod = 99;
        for i in 0..MAP_SLOTS {
            match src.entry(i) {
                Entry::Occupied(o) => {
                    assert_eq!(i, o.insert(i + add_mod));
                }
                Entry::Vacant(_) => {
                    panic!("Entry not found after insert");
                }
            }
        }
        for i in 0..MAP_SLOTS {
            match src.entry(i) {
                Entry::Occupied(o) => {
                    assert_eq!((i, i + add_mod), o.remove_entry());
                }
                Entry::Vacant(_) => {
                    panic!("Entry not found after insert");
                }
            }
        }
        for i in 0..MAP_SLOTS {
            assert!(matches!(src.entry(i), Entry::Vacant(_)));
        }
        assert!(src.is_empty());
    }

    #[test]
    fn first_last() {
        let mut map = FnvIndexMap::<_, _, 4>::new();

        assert_eq!(None, map.first());
        assert_eq!(None, map.last());

        map.insert(0, 0).unwrap();
        map.insert(2, 2).unwrap();

        assert_eq!(Some((&0, &0)), map.first());
        assert_eq!(Some((&2, &2)), map.last());

        map.insert(1, 1).unwrap();

        assert_eq!(Some((&1, &1)), map.last());

        *map.first_mut().unwrap().1 += 1;
        *map.last_mut().unwrap().1 += 1;

        assert_eq!(Some((&0, &1)), map.first());
        assert_eq!(Some((&1, &2)), map.last());
    }

    #[test]
    fn keys_iter() {
        let map = almost_filled_map();
        for (&key, i) in map.keys().zip(1..MAP_SLOTS) {
            assert_eq!(key, i);
        }
    }

    #[test]
    fn values_iter() {
        let map = almost_filled_map();
        for (&value, i) in map.values().zip(1..MAP_SLOTS) {
            assert_eq!(value, i);
        }
    }

    #[test]
    fn values_mut_iter() {
        let mut map = almost_filled_map();
        for value in map.values_mut() {
            *value += 1;
        }

        for (&value, i) in map.values().zip(1..MAP_SLOTS) {
            assert_eq!(value, i + 1);
        }
    }
}

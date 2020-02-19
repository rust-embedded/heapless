// NOTE this code has been based on slab (crates.io) v0.4.2

use core::{mem, slice};
use generic_array::ArrayLength;

use crate::Vec;

/// Implementation detail
#[doc(hidden)]
pub enum Entry<T> {
    Vacant(usize),
    Occupied(T),
}

/// TODO
pub struct Slab<T, N>
where
    N: ArrayLength<Entry<T>>,
{
    // entries: MaybeUninit<GenericArray<Entry<T>, N>>,
    entries: Vec<Entry<T>, N>,
    len: usize,
    next: usize,
}

impl<T, N> Slab<T, N>
where
    N: ArrayLength<Entry<T>>,
{
    /// TODO
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
            len: 0,
            next: 0,
        }
    }

    /// TODO
    pub fn insert(&mut self, val: T) -> Result<usize, T> {
        let key = self.next;
        self.insert_at(key, val)?;
        Ok(key)
    }

    fn insert_at(&mut self, key: usize, val: T) -> Result<(), T> {
        self.len += 1;

        if key == self.entries.len() {
            self.entries.push(Entry::Occupied(val)).map_err(|entry| {
                if let Entry::Occupied(val) = entry {
                    val
                } else {
                    unreachable!()
                }
            })?;
            self.next = key + 1;
        } else {
            let prev = mem::replace(&mut self.entries[key], Entry::Occupied(val));

            match prev {
                Entry::Vacant(next) => {
                    self.next = next;
                }
                _ => unreachable!(),
            }
        }

        Ok(())
    }

    /// TODO
    pub fn remove(&mut self, key: usize) -> T {
        // Swap the entry at the provided value
        let prev = mem::replace(&mut self.entries[key], Entry::Vacant(self.next));

        match prev {
            Entry::Occupied(val) => {
                self.len -= 1;
                self.next = key;
                val
            }
            _ => {
                // Woops, the entry is actually vacant, restore the state
                self.entries[key] = prev;
                panic!("invalid key");
            }
        }
    }

    /// TODO
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            entries: self.entries.iter_mut(),
            curr: 0,
        }
    }
}

impl<T, N> Default for Slab<T, N>
where
    N: ArrayLength<Entry<T>>,
{
    fn default() -> Self {
        Self::new()
    }
}

/// TODO
pub struct IterMut<'a, T> {
    entries: slice::IterMut<'a, Entry<T>>,
    curr: usize,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = (usize, &'a mut T);

    fn next(&mut self) -> Option<(usize, &'a mut T)> {
        while let Some(entry) = self.entries.next() {
            let curr = self.curr;
            self.curr += 1;

            if let Entry::Occupied(ref mut v) = *entry {
                return Some((curr, v));
            }
        }

        None
    }
}

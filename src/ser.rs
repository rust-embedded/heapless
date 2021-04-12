use crate::{
    sealed::{binary_heap::Kind as BinaryHeapKind, spsc::Uxx},
    BinaryHeapBase, IndexMapBase, IndexSetBase, LinearMapBase, StringBase, VecBase,
};
use hash32::{BuildHasher, Hash};
use serde::ser::{Serialize, SerializeMap, SerializeSeq, Serializer};

// Sequential containers

impl<T, KIND, U: Uxx, const N: usize> Serialize for BinaryHeapBase<T, KIND, U, N>
where
    T: Ord + Serialize,
    KIND: BinaryHeapKind,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.len()))?;
        for element in self {
            seq.serialize_element(element)?;
        }
        seq.end()
    }
}

impl<T, S, U: Uxx, const N: usize> Serialize for IndexSetBase<T, S, U, N>
where
    T: Eq + Hash + Serialize,
    S: BuildHasher,
{
    fn serialize<SER>(&self, serializer: SER) -> Result<SER::Ok, SER::Error>
    where
        SER: Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.len()))?;
        for element in self {
            seq.serialize_element(element)?;
        }
        seq.end()
    }
}

impl<T, U: Uxx, const N: usize> Serialize for VecBase<T, U, N>
where
    T: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.len()))?;
        for element in self {
            seq.serialize_element(element)?;
        }
        seq.end()
    }
}

// Dictionaries

impl<K, V, S, U: Uxx, const N: usize> Serialize for IndexMapBase<K, V, S, U, N>
where
    K: Eq + Hash + Serialize,
    S: BuildHasher,
    V: Serialize,
{
    fn serialize<SER>(&self, serializer: SER) -> Result<SER::Ok, SER::Error>
    where
        SER: Serializer,
    {
        let mut map = serializer.serialize_map(Some(self.len()))?;
        for (k, v) in self {
            map.serialize_entry(k, v)?;
        }
        map.end()
    }
}

impl<K, V, U: Uxx, const N: usize> Serialize for LinearMapBase<K, V, U, N>
where
    K: Eq + Serialize,
    V: Serialize,
{
    fn serialize<SER>(&self, serializer: SER) -> Result<SER::Ok, SER::Error>
    where
        SER: Serializer,
    {
        let mut map = serializer.serialize_map(Some(self.len()))?;
        for (k, v) in self {
            map.serialize_entry(k, v)?;
        }
        map.end()
    }
}

// String containers

impl<U: Uxx, const N: usize> Serialize for StringBase<U, N> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&*self)
    }
}

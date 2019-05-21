use generic_array::{typenum::PowerOfTwo, ArrayLength};
use hash32::{BuildHasher, Hash};
use serde::ser::{Serialize, SerializeMap, SerializeSeq, Serializer};

use crate::{
    sealed::binary_heap::Kind as BinaryHeapKind,
    indexmap::{Bucket, Pos},
    BinaryHeap, IndexMap, IndexSet, LinearMap, String, Vec,
};

// Sequential containers

impl<T, N, KIND> Serialize for BinaryHeap<T, N, KIND>
where
    T: Ord + Serialize,
    N: ArrayLength<T>,
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

impl<T, N, S> Serialize for IndexSet<T, N, S>
where
    T: Eq + Hash + Serialize,
    S: BuildHasher,
    N: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>> + PowerOfTwo,
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

impl<T, N> Serialize for Vec<T, N>
where
    T: Serialize,
    N: ArrayLength<T>,
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

impl<K, V, N, S> Serialize for IndexMap<K, V, N, S>
where
    K: Eq + Hash + Serialize,
    N: ArrayLength<Bucket<K, V>> + ArrayLength<Option<Pos>>,
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

impl<K, V, N> Serialize for LinearMap<K, V, N>
where
    N: ArrayLength<(K, V)>,
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

impl<N> Serialize for String<N>
where
    N: ArrayLength<u8>,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&*self)
    }
}

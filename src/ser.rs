use generic_array::{
    typenum::{IsLess, PowerOfTwo},
    ArrayLength,
};
use hash32::{BuildHasher, Hash};
use serde::ser::{Serialize, SerializeMap, SerializeSeq, Serializer};

use crate::{
    indexmap::{Bucket, Pos},
    sealed::binary_heap::Kind as BinaryHeapKind,
    vec::MaxCapacity,
    BinaryHeap, IndexMap, IndexSet, LinearMap, String, Vec,
};

// Sequential containers

impl<T, N, KIND, U> Serialize for BinaryHeap<T, N, KIND, U>
where
    T: Ord + Serialize,
    N: ArrayLength<T> + IsLess<U::Cap>,
    KIND: BinaryHeapKind,
    U: MaxCapacity,
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

impl<T, N, S, U> Serialize for IndexSet<T, N, S, U>
where
    T: Eq + Hash + Serialize,
    S: BuildHasher,
    N: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>> + PowerOfTwo + IsLess<U::Cap>,
    U: MaxCapacity,
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

impl<T, N, U> Serialize for Vec<T, N, U>
where
    T: Serialize,
    N: ArrayLength<T> + IsLess<U::Cap>,
    U: MaxCapacity,
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

impl<K, V, N, S, U> Serialize for IndexMap<K, V, N, S, U>
where
    K: Eq + Hash + Serialize,
    N: ArrayLength<Bucket<K, V>> + ArrayLength<Option<Pos>> + IsLess<U::Cap>,
    S: BuildHasher,
    V: Serialize,
    U: MaxCapacity,
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

impl<K, V, N, U> Serialize for LinearMap<K, V, N, U>
where
    N: ArrayLength<(K, V)> + IsLess<U::Cap>,
    K: Eq + Serialize,
    V: Serialize,
    U: MaxCapacity,
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

impl<N, U> Serialize for String<N, U>
where
    N: ArrayLength<u8> + IsLess<U::Cap>,
    U: MaxCapacity,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&*self)
    }
}

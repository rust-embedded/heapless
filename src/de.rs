use core::{fmt, marker::PhantomData};

use generic_array::{typenum::PowerOfTwo, ArrayLength};
use hash32::{BuildHasherDefault, Hash, Hasher};
use serde::de::{self, Deserialize, Deserializer, Error, MapAccess, SeqAccess};

use crate::{
    sealed::binary_heap::Kind as BinaryHeapKind,
    indexmap::{Bucket, Pos},
    BinaryHeap, IndexMap, IndexSet, LinearMap, String, Vec,
};

// Sequential containers

impl<'de, T, N, KIND> Deserialize<'de> for BinaryHeap<T, N, KIND>
where
    T: Ord + Deserialize<'de>,
    N: ArrayLength<T>,
    KIND: BinaryHeapKind,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ValueVisitor<'de, T, N, KIND>(PhantomData<(&'de (), T, N, KIND)>);

        impl<'de, T, N, KIND> de::Visitor<'de> for ValueVisitor<'de, T, N, KIND>
        where
            T: Ord + Deserialize<'de>,
            N: ArrayLength<T>,
            KIND: BinaryHeapKind,
        {
            type Value = BinaryHeap<T, N, KIND>;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a sequence")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                let mut values = BinaryHeap::new();

                while let Some(value) = seq.next_element()? {
                    if values.push(value).is_err() {
                        return Err(A::Error::invalid_length(values.capacity() + 1, &self))?;
                    }
                }

                Ok(values)
            }
        }
        deserializer.deserialize_seq(ValueVisitor(PhantomData))
    }
}

impl<'de, T, N, S> Deserialize<'de> for IndexSet<T, N, BuildHasherDefault<S>>
where
    T: Eq + Hash + Deserialize<'de>,
    S: Hasher + Default,
    N: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>> + PowerOfTwo,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ValueVisitor<'de, T, N, S>(PhantomData<(&'de (), T, N, S)>);

        impl<'de, T, N, S> de::Visitor<'de> for ValueVisitor<'de, T, N, S>
        where
            T: Eq + Hash + Deserialize<'de>,
            S: Hasher + Default,
            N: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>> + PowerOfTwo,
        {
            type Value = IndexSet<T, N, BuildHasherDefault<S>>;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a sequence")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                let mut values = IndexSet::new();

                while let Some(value) = seq.next_element()? {
                    if values.insert(value).is_err() {
                        return Err(A::Error::invalid_length(values.capacity() + 1, &self))?;
                    }
                }

                Ok(values)
            }
        }
        deserializer.deserialize_seq(ValueVisitor(PhantomData))
    }
}

impl<'de, T, N> Deserialize<'de> for Vec<T, N>
where
    N: ArrayLength<T>,
    T: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ValueVisitor<'de, T, N>(PhantomData<(&'de (), T, N)>);

        impl<'de, T, N> de::Visitor<'de> for ValueVisitor<'de, T, N>
        where
            N: ArrayLength<T>,
            T: Deserialize<'de>,
        {
            type Value = Vec<T, N>;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a sequence")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                let mut values = Vec::new();

                while let Some(value) = seq.next_element()? {
                    if values.push(value).is_err() {
                        return Err(A::Error::invalid_length(values.capacity() + 1, &self))?;
                    }
                }

                Ok(values)
            }
        }
        deserializer.deserialize_seq(ValueVisitor(PhantomData))
    }
}

// Dictionaries

impl<'de, K, V, N, S> Deserialize<'de> for IndexMap<K, V, N, BuildHasherDefault<S>>
where
    K: Eq + Hash + Deserialize<'de>,
    V: Deserialize<'de>,
    N: ArrayLength<Bucket<K, V>> + ArrayLength<Option<Pos>> + PowerOfTwo,
    S: Default + Hasher,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ValueVisitor<'de, K, V, N, S>(PhantomData<(&'de (), K, V, N, S)>);

        impl<'de, K, V, N, S> de::Visitor<'de> for ValueVisitor<'de, K, V, N, S>
        where
            K: Eq + Hash + Deserialize<'de>,
            V: Deserialize<'de>,
            N: ArrayLength<Bucket<K, V>> + ArrayLength<Option<Pos>> + PowerOfTwo,
            S: Default + Hasher,
        {
            type Value = IndexMap<K, V, N, BuildHasherDefault<S>>;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a map")
            }

            fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
            where
                A: MapAccess<'de>,
            {
                let mut values = IndexMap::new();

                while let Some((key, value)) = map.next_entry()? {
                    if values.insert(key, value).is_err() {
                        return Err(A::Error::invalid_length(values.capacity() + 1, &self))?;
                    }
                }

                Ok(values)
            }
        }
        deserializer.deserialize_seq(ValueVisitor(PhantomData))
    }
}

impl<'de, K, V, N> Deserialize<'de> for LinearMap<K, V, N>
where
    K: Eq + Deserialize<'de>,
    V: Deserialize<'de>,
    N: ArrayLength<(K, V)>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ValueVisitor<'de, K, V, N>(PhantomData<(&'de (), K, V, N)>);

        impl<'de, K, V, N> de::Visitor<'de> for ValueVisitor<'de, K, V, N>
        where
            K: Eq + Deserialize<'de>,
            V: Deserialize<'de>,
            N: ArrayLength<(K, V)>,
        {
            type Value = LinearMap<K, V, N>;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a map")
            }

            fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
            where
                A: MapAccess<'de>,
            {
                let mut values = LinearMap::new();

                while let Some((key, value)) = map.next_entry()? {
                    if values.insert(key, value).is_err() {
                        return Err(A::Error::invalid_length(values.capacity() + 1, &self))?;
                    }
                }

                Ok(values)
            }
        }
        deserializer.deserialize_seq(ValueVisitor(PhantomData))
    }
}

// String containers

impl<'de, N> Deserialize<'de> for String<N>
where
    N: ArrayLength<u8>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ValueVisitor<'de, N>(PhantomData<(&'de (), N)>);

        impl<'de, N> de::Visitor<'de> for ValueVisitor<'de, N>
        where
            N: ArrayLength<u8>,
        {
            type Value = String<N>;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(
                    formatter,
                    "a string no more than {} bytes long",
                    N::to_u64()
                )
            }

            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                let mut s = String::new();
                s.push_str(v)
                    .map_err(|_| E::invalid_length(v.len(), &self))?;
                Ok(s)
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                let mut bytes = Vec::new();
                if bytes.extend_from_slice(v).is_err() {
                    return Err(E::invalid_value(de::Unexpected::Bytes(v), &self));
                }

                String::from_utf8(bytes)
                    .map_err(|_| E::invalid_value(de::Unexpected::Bytes(v), &self))
            }
        }

        deserializer.deserialize_str(ValueVisitor::<'de, N>(PhantomData))
    }
}

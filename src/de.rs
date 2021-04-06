use core::{fmt, marker::PhantomData};

use generic_array::{typenum::PowerOfTwo, ArrayLength};
use hash32::{BuildHasherDefault, Hash, Hasher};
use serde::de::{self, Deserialize, Deserializer, Error, MapAccess, SeqAccess};

use crate::{
    indexmap::{Bucket, Pos},
    sealed::binary_heap::Kind as BinaryHeapKind,
    BinaryHeap, IndexMap, IndexSet, LinearMap, String, Vec,
};

// Sequential containers

impl<'de, T, N, KIND, U> Deserialize<'de> for BinaryHeap<T, N, KIND, U>
where
    T: Ord + Deserialize<'de>,
    N: ArrayLength<T>,
    KIND: BinaryHeapKind,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ValueVisitor<'de, T, N, KIND, U>(PhantomData<(&'de (), T, N, KIND, U)>);

        impl<'de, T, N, KIND, U> de::Visitor<'de> for ValueVisitor<'de, T, N, KIND, U>
        where
            T: Ord + Deserialize<'de>,
            N: ArrayLength<T>,
            KIND: BinaryHeapKind,
        {
            type Value = BinaryHeap<T, N, KIND, U>;

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

impl<'de, T, N, S, U> Deserialize<'de> for IndexSet<T, N, BuildHasherDefault<S>, U>
where
    T: Eq + Hash + Deserialize<'de>,
    S: Hasher + Default,
    N: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>> + PowerOfTwo,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ValueVisitor<'de, T, N, S, U>(PhantomData<(&'de (), T, N, S, U)>);

        impl<'de, T, N, S, U> de::Visitor<'de> for ValueVisitor<'de, T, N, S, U>
        where
            T: Eq + Hash + Deserialize<'de>,
            S: Hasher + Default,
            N: ArrayLength<Bucket<T, ()>> + ArrayLength<Option<Pos>> + PowerOfTwo,
        {
            type Value = IndexSet<T, N, BuildHasherDefault<S>, U>;

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

impl<'de, T, N, U> Deserialize<'de> for Vec<T, N, U>
where
    N: ArrayLength<T>,
    T: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ValueVisitor<'de, T, N, U>(PhantomData<(&'de (), T, N, U)>);

        impl<'de, T, N, U> de::Visitor<'de> for ValueVisitor<'de, T, N, U>
        where
            N: ArrayLength<T>,
            T: Deserialize<'de>,
        {
            type Value = Vec<T, N, U>;

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

impl<'de, K, V, N, S, U> Deserialize<'de> for IndexMap<K, V, N, BuildHasherDefault<S>, U>
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
        struct ValueVisitor<'de, K, V, N, S, U>(PhantomData<(&'de (), K, V, N, S, U)>);

        impl<'de, K, V, N, S, U> de::Visitor<'de> for ValueVisitor<'de, K, V, N, S, U>
        where
            K: Eq + Hash + Deserialize<'de>,
            V: Deserialize<'de>,
            N: ArrayLength<Bucket<K, V>> + ArrayLength<Option<Pos>> + PowerOfTwo,
            S: Default + Hasher,
        {
            type Value = IndexMap<K, V, N, BuildHasherDefault<S>, U>;

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
        deserializer.deserialize_map(ValueVisitor(PhantomData))
    }
}

impl<'de, K, V, N, U> Deserialize<'de> for LinearMap<K, V, N, U>
where
    K: Eq + Deserialize<'de>,
    V: Deserialize<'de>,
    N: ArrayLength<(K, V)>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ValueVisitor<'de, K, V, N, U>(PhantomData<(&'de (), K, V, N, U)>);

        impl<'de, K, V, N, U> de::Visitor<'de> for ValueVisitor<'de, K, V, N, U>
        where
            K: Eq + Deserialize<'de>,
            V: Deserialize<'de>,
            N: ArrayLength<(K, V)>,
        {
            type Value = LinearMap<K, V, N, U>;

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
        deserializer.deserialize_map(ValueVisitor(PhantomData))
    }
}

// String containers

impl<'de, N, U> Deserialize<'de> for String<N, U>
where
    N: ArrayLength<u8>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ValueVisitor<'de, N, U>(PhantomData<(&'de (), N, U)>);

        impl<'de, N, U> de::Visitor<'de> for ValueVisitor<'de, N, U>
        where
            N: ArrayLength<u8>,
        {
            type Value = String<N, U>;

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

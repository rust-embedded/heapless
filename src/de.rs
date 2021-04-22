use crate::{
    sealed::{binary_heap::Kind as BinaryHeapKind, spsc::Uxx},
    BinaryHeapBase, IndexMapBase, IndexSetBase, LinearMapBase, StringBase, VecBase,
};
use core::{fmt, marker::PhantomData};
use hash32::{BuildHasherDefault, Hash, Hasher};
use serde::de::{self, Deserialize, Deserializer, Error, MapAccess, SeqAccess};

// Sequential containers

impl<'de, T, KIND, U: Uxx, const N: usize> Deserialize<'de> for BinaryHeapBase<T, KIND, U, N>
where
    T: Ord + Deserialize<'de>,

    KIND: BinaryHeapKind,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ValueVisitor<'de, T, KIND, U: Uxx, const N: usize>(
            PhantomData<(&'de (), T, KIND, U)>,
        );

        impl<'de, T, KIND, U: Uxx, const N: usize> de::Visitor<'de> for ValueVisitor<'de, T, KIND, U, N>
        where
            T: Ord + Deserialize<'de>,
            KIND: BinaryHeapKind,
        {
            type Value = BinaryHeapBase<T, KIND, U, N>;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a sequence")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                let mut values = BinaryHeapBase::default();

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

impl<'de, T, S, U: Uxx, const N: usize> Deserialize<'de>
    for IndexSetBase<T, BuildHasherDefault<S>, U, N>
where
    T: Eq + Hash + Deserialize<'de>,
    S: Hasher + Default,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ValueVisitor<'de, T, S, U: Uxx, const N: usize>(PhantomData<(&'de (), T, S, U)>);

        impl<'de, T, S, U: Uxx, const N: usize> de::Visitor<'de> for ValueVisitor<'de, T, S, U, N>
        where
            T: Eq + Hash + Deserialize<'de>,
            S: Hasher + Default,
        {
            type Value = IndexSetBase<T, BuildHasherDefault<S>, U, N>;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a sequence")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                let mut values = IndexSetBase::new();

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

impl<'de, T, U: Uxx, const N: usize> Deserialize<'de> for VecBase<T, U, N>
where
    T: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ValueVisitor<'de, T, U: Uxx, const N: usize>(PhantomData<(&'de (), T, U)>);

        impl<'de, T, U: Uxx, const N: usize> serde::de::Visitor<'de> for ValueVisitor<'de, T, U, N>
        where
            T: Deserialize<'de>,
        {
            type Value = VecBase<T, U, N>;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a sequence")
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: SeqAccess<'de>,
            {
                let mut values = VecBase::default();

                while let Some(value) = seq.next_element()? {
                    if values.push(value).is_err() {
                        return Err(A::Error::invalid_length(
                            values.capacity_nonconst() + 1,
                            &self,
                        ))?;
                    }
                }

                Ok(values)
            }
        }
        deserializer.deserialize_seq(ValueVisitor(PhantomData))
    }
}

// Dictionaries

impl<'de, K, V, S, U: Uxx, const N: usize> Deserialize<'de>
    for IndexMapBase<K, V, BuildHasherDefault<S>, U, N>
where
    K: Eq + Hash + Deserialize<'de>,
    V: Deserialize<'de>,
    S: Default + Hasher,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ValueVisitor<'de, K, V, S, U: Uxx, const N: usize>(
            PhantomData<(&'de (), K, V, S, U)>,
        );

        impl<'de, K, V, S, U: Uxx, const N: usize> de::Visitor<'de> for ValueVisitor<'de, K, V, S, U, N>
        where
            K: Eq + Hash + Deserialize<'de>,
            V: Deserialize<'de>,
            S: Default + Hasher,
        {
            type Value = IndexMapBase<K, V, BuildHasherDefault<S>, U, N>;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a map")
            }

            fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
            where
                A: MapAccess<'de>,
            {
                let mut values = IndexMapBase::default();

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

impl<'de, K, V, U: Uxx, const N: usize> Deserialize<'de> for LinearMapBase<K, V, U, N>
where
    K: Eq + Deserialize<'de>,
    V: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ValueVisitor<'de, K, V, U: Uxx, const N: usize>(PhantomData<(&'de (), K, V, U)>);

        impl<'de, K, V, U: Uxx, const N: usize> de::Visitor<'de> for ValueVisitor<'de, K, V, U, N>
        where
            K: Eq + Deserialize<'de>,
            V: Deserialize<'de>,
        {
            type Value = LinearMapBase<K, V, U, N>;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a map")
            }

            fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
            where
                A: MapAccess<'de>,
            {
                let mut values = LinearMapBase::default();

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

impl<'de, U: Uxx, const N: usize> Deserialize<'de> for StringBase<U, N> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ValueVisitor<'de, U: Uxx, const N: usize>(PhantomData<(&'de (), U)>);

        impl<'de, U: Uxx, const N: usize> de::Visitor<'de> for ValueVisitor<'de, U, N> {
            type Value = StringBase<U, N>;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(formatter, "a string no more than {} bytes long", N as u64)
            }

            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                let mut s = StringBase::default();
                s.push_str(v)
                    .map_err(|_| E::invalid_length(v.len(), &self))?;
                Ok(s)
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                let mut s = StringBase::default();

                s.push_str(
                    core::str::from_utf8(v)
                        .map_err(|_| E::invalid_value(de::Unexpected::Bytes(v), &self))?,
                )
                .map_err(|_| E::invalid_length(v.len(), &self))?;

                Ok(s)
            }
        }

        deserializer.deserialize_str(ValueVisitor::<'de, U, N>(PhantomData))
    }
}

use core::{fmt, marker};

use generic_array::{ArrayLength, GenericArray};
use serde::Deserializer;
use serde::de::{Error, Visitor};

use crate::{ByteBuf, Vec};

/// Types that can be deserialized via `#[serde(with = "heapless::serde_as_bytes")]`.
pub trait Deserialize<'de>: Sized {
    #[allow(missing_docs)]
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>;
}

impl<'de: 'a, 'a> Deserialize<'de> for &'a [u8] {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        // Via the serde::Deserialize impl for &[u8].
        serde::Deserialize::deserialize(deserializer)
    }
}

impl<'de, N> Deserialize<'de> for GenericArray<u8, N>
where
    N: ArrayLength<u8>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ValueVisitor<'de, N>(marker::PhantomData<(&'de (), N)>);

        impl<'de, N> serde::de::Visitor<'de> for ValueVisitor<'de, N>
        where
            N: ArrayLength<u8>,
        {
            type Value = GenericArray<u8, N>;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a sequence")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                if v.len() > N::to_usize() {
                    return Err(E::invalid_length(v.len(), &self))?;
                }
                Ok(GenericArray::clone_from_slice(v))
            }
        }

        deserializer.deserialize_bytes(ValueVisitor(marker::PhantomData))
    }
}

impl<'de, N> Deserialize<'de> for Vec<u8, N>
where
    N: ArrayLength<u8>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Deserialize::deserialize(deserializer).map(ByteBuf::into_inner)
    }
}

impl<'de, N> Deserialize<'de> for ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        // Via the serde::Deserialize impl for ByteBuf.
        serde::Deserialize::deserialize(deserializer)
    }
}

// #[cfg(any(feature = "std", feature = "alloc"))]
// impl<'de> Deserialize<'de> for Box<[u8]> {
//     fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
//     where
//         D: Deserializer<'de>,
//     {
//         Deserialize::deserialize(deserializer).map(Vec::into_boxed_slice)
//     }
// }

// #[cfg(any(feature = "std", feature = "alloc"))]
// impl<'de> Deserialize<'de> for Box<Bytes> {
//     fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
//     where
//         D: Deserializer<'de>,
//     {
//         let bytes: Box<[u8]> = Deserialize::deserialize(deserializer)?;
//         Ok(bytes.into())
//     }
// }

impl<'de, T> Deserialize<'de> for Option<T>
where
    T: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct BytesVisitor<T> {
            out: marker::PhantomData<T>,
        }

        impl<'de, T> Visitor<'de> for BytesVisitor<T>
        where
            T: Deserialize<'de>,
        {
            type Value = Option<T>;

            fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("optional byte array")
            }

            fn visit_unit<E: Error>(self) -> Result<Self::Value, E> {
                Ok(None)
            }

            fn visit_none<E: Error>(self) -> Result<Self::Value, E> {
                Ok(None)
            }

            fn visit_some<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
            where
                D: Deserializer<'de>,
            {
                T::deserialize(deserializer).map(Some)
            }
        }

        let visitor = BytesVisitor { out: marker::PhantomData };
        deserializer.deserialize_option(visitor)
    }
}

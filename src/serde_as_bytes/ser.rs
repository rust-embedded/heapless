use generic_array::ArrayLength;
use serde::Serializer;

/// Types that can be serialized via `#[serde(with = "heapless::serde_as_bytes")]`.
pub trait Serialize {
    #[allow(missing_docs)]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer;
}

impl Serialize for [u8] {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_bytes(self)
    }
}

impl<N> Serialize for crate::Vec<u8, N>
where
    N: ArrayLength<u8>
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_bytes(self)
    }
}

impl<N> Serialize for crate::ByteBuf<N>
where
    N: ArrayLength<u8>
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_bytes(self)
    }
}

impl<'a, T> Serialize for &'a T
where
    T: ?Sized + Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        (**self).serialize(serializer)
    }
}

impl<T> Serialize for crate::pool::Box<T, crate::pool::Init>
where
    T: Sized + Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        (**self).serialize(serializer)
    }
}

impl<T> Serialize for Option<T>
where
    T: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        struct AsBytes<T>(T);

        impl<T> serde::Serialize for AsBytes<T>
        where
            T: Serialize,
        {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                self.0.serialize(serializer)
            }
        }

        match self {
            Some(b) => serializer.serialize_some(&AsBytes(b)),
            None => serializer.serialize_none(),
        }
    }
}

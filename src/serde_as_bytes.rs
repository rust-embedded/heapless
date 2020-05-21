//! Wrapper types to enable optimized handling of `&[u8]` and `Vec<u8, N>`.
//!
//! This code is an adaption of the `serde_bytes` library code.
//!
//! Without specialization, Rust forces Serde to treat `&[u8]` just like any
//! other slice and `Vec<u8, N>` just like any other vector. In reality this
//! particular slice and vector can often be serialized and deserialized in a
//! more efficient, compact representation in many formats.
//!
//! When working with such a format, you can opt into specialized handling of
//! `Vec<u8, N>` by wrapping it in `heapless::ByteBuf`.
//!
//! Additionally this crate supports the Serde `with` attribute to enable
//! efficient handling of `&[u8]` and `Vec<u8, N>` in structs without needing a
//! wrapper type.
//!
//! ```
//! # use generic_array::ArrayLength;
//! # use serde_derive::{Deserialize, Serialize};
//! use heapless::Vec;
//! use serde::{Deserialize, Serialize};
//!
//! #[derive(Deserialize, Serialize)]
//! struct Efficient<'a, N>
//! where
//!     N: ArrayLength<u8>,
//! {
//!     #[serde(with = "heapless::serde_as_bytes")]
//!     bytes: &'a [u8],
//!
//!     #[serde(with = "heapless::serde_as_bytes")]
//!     byte_buf: Vec<u8, N>,
//! }
//! ```
mod de;
mod ser;

pub use de::Deserialize;
pub use ser::Serialize;

use serde::Serializer;
use serde::Deserializer;

/// Serde `serialize_with` function to serialize bytes efficiently.
///
/// This function can be used with either of the following Serde attributes:
///
/// - `#[serde(with = "heapless::serde_as_bytes")]`
/// - `#[serde(serialize_with = "heapless::serde_as_bytes::serialize")]`
///
/// ```
/// # use generic_array::ArrayLength;
/// # use serde_derive::Serialize;
/// use heapless::Vec;
/// use serde::Serialize;
///
/// #[derive(Serialize)]
/// struct Efficient<'a, N>
/// where
///     N: ArrayLength<u8>,
/// {
///     #[serde(with = "heapless::serde_as_bytes")]
///     bytes: &'a [u8],
///
///     #[serde(with = "heapless::serde_as_bytes")]
///     byte_buf: heapless::Vec<u8, N>,
/// }
/// ```
#[cfg(feature = "serde")]
pub fn serialize<T, S>(bytes: &T, serializer: S) -> Result<S::Ok, S::Error>
where
    T: ?Sized + Serialize,
    S: Serializer,
{
    Serialize::serialize(bytes, serializer)
}

/// Serde `deserialize_with` function to deserialize bytes efficiently.
///
/// This function can be used with either of the following Serde attributes:
///
/// - `#[serde(with = "heapless::serde_as_bytes")]`
/// - `#[serde(deserialize_with = "heapless::serde_as_bytes::deserialize")]`
///
/// ```
/// # use generic_array::ArrayLength;
/// # use serde_derive::Deserialize;
/// use heapless::Vec;
/// use serde::Deserialize;
///
/// #[derive(Deserialize)]
/// struct Packet<N>
/// where
///     N: ArrayLength<u8>,
/// {
///     #[serde(with = "heapless::serde_as_bytes")]
///     payload: Vec<u8, N>,
/// }
/// ```
#[cfg(feature = "serde")]
pub fn deserialize<'de, T, D>(deserializer: D) -> Result<T, D::Error>
where
    T: Deserialize<'de>,
    D: Deserializer<'de>,
{
    Deserialize::deserialize(deserializer)
}
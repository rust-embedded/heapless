#![cfg(feature = "serde")]

use heapless::{ByteBuf, consts::*, Vec};
use serde::{Deserialize, Serialize};
use serde_derive::{Deserialize, Serialize};

// CBOR has a specialized "bytes" string type.
// For this format, a general Vec<T, N> gets serialized
// as a sequence of u8, while ByteBuf<N>, and Vec<T, N>
// decorated with `#[serde(with = "heapless::serde_as_bytes")`
// get serialized as bytes string

const BYTES_SERIALIZATION: &'static [u8] =
    b"\xa2ebytesC\x01\x02\x03hbyte_bufC\x01\x02\x03";
const SEQUENCE_SERIALIZATION_NO_SLICE: &'static [u8] =
    b"\xa1hbyte_buf\x83\x01\x02\x03";
const SEQUENCE_SERIALIZATION: &'static [u8] =
    b"\xa2ebytes\x83\x01\x02\x03hbyte_buf\x83\x01\x02\x03";

#[derive(Debug, Deserialize, Serialize, PartialEq)]
struct AsBytes<'a>
{
    #[serde(with = "heapless::serde_as_bytes")]
    bytes: &'a [u8],

    #[serde(with = "heapless::serde_as_bytes")]
    byte_buf: Vec<u8, U3>,
}

#[derive(Debug, Deserialize, Serialize, PartialEq)]
struct RawVec<'a>
{
    bytes: &'a [u8],
    byte_buf: Vec<u8, U3>,
}

#[derive(Debug, Deserialize, Serialize, PartialEq)]
struct RawVecNoSlice
{
    byte_buf: Vec<u8, U3>,
}

#[derive(Debug, Deserialize, Serialize, PartialEq)]
struct RawBytes<'a>
{
    #[serde(with = "heapless::serde_as_bytes")]
    bytes: &'a [u8],
    byte_buf: ByteBuf<U3>,
}

fn cbor_serialize<T: Serialize>(object: &T, buffer: &mut [u8])
    -> Result<usize, serde_cbor::Error>
{
    let writer = serde_cbor::ser::SliceWrite::new(buffer);
    let mut ser = serde_cbor::Serializer::new(writer);
    object.serialize(&mut ser)?;
    Ok(ser.into_inner().bytes_written())
}

fn cbor_deserialize<'a, T: Deserialize<'a>>(buffer: &'a mut [u8])
    -> Result<T, serde_cbor::Error>
{
    serde_cbor::de::from_mut_slice(buffer)
}

#[test]
fn cbor() {
    let as_bytes = AsBytes {
        bytes: &[1, 2, 3],
        byte_buf: Vec::from_slice(&[1, 2, 3]).unwrap(),
    };
    let raw_vec = RawVec {
        bytes: &[1, 2, 3],
        byte_buf: Vec::from_slice(&[1, 2, 3]).unwrap(),
    };
    let raw_vec_no_slice = RawVecNoSlice {
        byte_buf: Vec::from_slice(&[1, 2, 3]).unwrap(),
    };
    let raw_bytes = RawBytes {
        bytes: &[1, 2, 3],
        byte_buf: ByteBuf::from_slice(&[1, 2, 3]).unwrap(),
    };

    let mut ser_as_bytes = ByteBuf::<U100>::try_read(|buf| cbor_serialize(&as_bytes, buf)).unwrap();
    assert_eq!(ser_as_bytes, BYTES_SERIALIZATION);
    assert_eq!(as_bytes, cbor_deserialize(&mut *ser_as_bytes).unwrap());

    let ser_raw_vec = ByteBuf::<U100>::try_read(|buf| cbor_serialize(&raw_vec, buf)).unwrap();
    assert_eq!(ser_raw_vec, SEQUENCE_SERIALIZATION);

    let mut ser_raw_vec_no_slice = ByteBuf::<U100>::try_read(|buf| cbor_serialize(&raw_vec_no_slice, buf)).unwrap();
    assert_eq!(ser_raw_vec_no_slice, SEQUENCE_SERIALIZATION_NO_SLICE);
    assert_eq!(raw_vec_no_slice, cbor_deserialize(&mut *ser_raw_vec_no_slice).unwrap());

    let mut ser_raw_bytes = ByteBuf::<U100>::try_read(|buf| cbor_serialize(&raw_bytes, buf)).unwrap();
    assert_eq!(ser_as_bytes, BYTES_SERIALIZATION);
    assert_eq!(raw_bytes, cbor_deserialize(&mut *ser_raw_bytes).unwrap());
}
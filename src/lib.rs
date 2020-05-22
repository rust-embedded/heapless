//! `static` friendly data structures that don't require dynamic memory allocation
//!
//! The core principle behind `heapless` is that its data structures are backed by a *static* memory
//! allocation. For example, you can think of `heapless::Vec` as an alternative version of
//! `std::Vec` with fixed capacity and that can't be re-allocated on the fly (e.g. via `push`).
//!
//! All `heapless` data structures store their memory allocation *inline* and specify their capacity
//! via their type parameter `N`. This means that you can instantiate a `heapless` data structure on
//! the stack, in a `static` variable, or even in the heap.
//!
//! ```
//! use heapless::Vec; // fixed capacity `std::Vec`
//! use heapless::consts::U8; // type level integer used to specify capacity
//!
//! // on the stack
//! let mut xs: Vec<u8, U8> = Vec::new(); // can hold up to 8 elements
//! xs.push(42).unwrap();
//! assert_eq!(xs.pop(), Some(42));
//!
//! // in a `static` variable
//! // (because `const-fn` has not been fully stabilized you need to use the helper structs in
//! // the `i` module, which must be wrapped in a tuple struct)
//! static mut XS: Vec<u8, U8> = Vec(heapless::i::Vec::new());
//!
//! let xs = unsafe { &mut XS };
//!
//! xs.push(42);
//! assert_eq!(xs.pop(), Some(42));
//!
//! // in the heap (though kind of pointless because no reallocation)
//! let mut ys: Box<Vec<u8, U8>> = Box::new(Vec::new());
//! ys.push(42).unwrap();
//! assert_eq!(ys.pop(), Some(42));
//! ```
//!
//! Because they have fixed capacity `heapless` data structures don't implicitly reallocate. This
//! means that operations like `heapless::Vec.push` are *truly* constant time rather than amortized
//! constant time with potentially unbounded (depends on the allocator) worst case execution time
//! (which is bad / unacceptable for hard real time applications).
//!
//! `heapless` data structures don't use a memory allocator which means no risk of an uncatchable
//! Out Of Memory (OOM) condition while performing operations on them. It's certainly possible to
//! run out of capacity while growing `heapless` data structures, but the API lets you handle this
//! possibility by returning a `Result` on operations that may exhaust the capacity of the data
//! structure.
//!
//! List of currently implemented data structures:
//!
//! - [`BinaryHeap`](binary_heap/struct.BinaryHeap.html) -- priority queue
//! - [`ByteBuf`](struct.ByteBuf.html)
//! - [`IndexMap`](struct.IndexMap.html) -- hash table
//! - [`IndexSet`](struct.IndexSet.html) -- hash set
//! - [`LinearMap`](struct.LinearMap.html)
//! - [`Pool`](pool/struct.Pool.html) -- lock-free memory pool
//! - [`String`](struct.String.html)
//! - [`Vec`](struct.Vec.html)
//! - [`mpmc::Q*`](mpmc/index.html) -- multiple producer multiple consumer lock-free queue
//! - [`spsc::Queue`](spsc/struct.Queue.html) -- single producer single consumer lock-free queue
//!
//! # Optional Features
//!
//! The `heapless` crate provides the following optional Cargo features:
//!
//! - [`serde`]: Implement `serde::Serialize` and `serde::Deserialize` for
//!   `ByteBuf<N>`, `String<N>` and `Vec<u8, N>`
//!
//! [`serde`]: https://serde.rs/
//!
//! - [`ufmt`]: Implement `ufmt::uWrite` and `ufmt::uDebug` for
//!   `ByteBuf<N>`, `String<N>` and `Vec<u8, N>`
//!
//! [`ufmt`]: https://docs.rs/ufmt/
//!
//! # Minimum Supported Rust Version (MSRV)
//!
//! This crate is guaranteed to compile on stable Rust 1.36 and up with its default set of features.
//! It *might* compile on older versions but that may change in any new patch release.

#![cfg_attr(not(test), no_std)]
#![deny(missing_docs)]
#![deny(rust_2018_compatibility)]
#![deny(rust_2018_idioms)]
#![deny(warnings)]

pub use binary_heap::BinaryHeap;
pub use bytebuf::ByteBuf;
pub use generic_array::typenum::{consts, PowerOfTwo, Unsigned};
pub use generic_array::ArrayLength;
pub use indexmap::{Bucket, FnvIndexMap, IndexMap, Pos};
pub use indexset::{FnvIndexSet, IndexSet};
pub use linear_map::LinearMap;
pub use string::String;
pub use vec::Vec;
pub use histbuf::HistoryBuffer;

mod bytebuf;
// NOTE this code was last ported from v0.4.1 of the indexmap crate
mod indexmap;
mod indexset;
mod linear_map;
mod string;
mod vec;
mod histbuf;

#[cfg(feature = "serde")]
mod de;
#[cfg(feature = "serde")]
mod ser;
#[cfg(feature = "serde")]
pub mod serde_as_bytes;

pub mod binary_heap;
pub mod i;
#[cfg(all(has_cas, feature = "cas"))]
pub mod mpmc;
#[cfg(all(has_cas, feature = "cas"))]
pub mod pool;
#[cfg(has_atomics)]
pub mod spsc;

#[cfg(feature = "ufmt")]
mod ufmt;

mod sealed;

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
//!
//! // on the stack
//! let mut xs: Vec<u8, 8> = Vec::new(); // can hold up to 8 elements
//! xs.push(42).unwrap();
//! assert_eq!(xs.pop(), Some(42));
//!
//! // in a `static` variable
//! static mut XS: Vec<u8, 8> = Vec::new();
//!
//! let xs = unsafe { &mut XS };
//!
//! xs.push(42);
//! assert_eq!(xs.pop(), Some(42));
//!
//! // in the heap (though kind of pointless because no reallocation)
//! let mut ys: Box<Vec<u8, 8>> = Box::new(Vec::new());
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
//! - [`Arc`](pool/singleton/arc/struct.Arc.html) -- Thread-safe reference-counting pointer backed by a memory pool
//! - [`BinaryHeap`](binary_heap/struct.BinaryHeap.html) -- priority queue
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
//! - `ufmt-impl`: Implement [`ufmt_write::uWrite`] for `String<N>` and `Vec<u8, N>`
//!
//! [`ufmt_write::uWrite`]: https://docs.rs/ufmt-write/
//!
//! # Minimum Supported Rust Version (MSRV)
//!
//! This crate is guaranteed to compile on stable Rust 1.51 and up with its default set of features.
//! It *might* compile on older versions but that may change in any new patch release.

#![cfg_attr(not(test), no_std)]
#![deny(missing_docs)]
#![deny(rust_2018_compatibility)]
#![deny(rust_2018_idioms)]
#![deny(warnings)]
#![deny(const_err)]

pub use binary_heap::BinaryHeap;
pub use deque::Deque;
pub use histbuf::{HistoryBuffer, OldestOrdered};
pub use indexmap::{Bucket, Entry, FnvIndexMap, IndexMap, OccupiedEntry, Pos, VacantEntry};
pub use indexset::{FnvIndexSet, IndexSet};
pub use linear_map::LinearMap;
#[cfg(all(has_cas, feature = "cas"))]
pub use pool::singleton::arc::Arc;
pub use string::String;
pub use vec::Vec;

#[macro_use]
#[cfg(test)]
mod test_helpers;

mod deque;
mod histbuf;
mod indexmap;
mod indexset;
mod linear_map;
mod string;
mod vec;

#[cfg(feature = "serde")]
mod de;
#[cfg(feature = "serde")]
mod ser;

pub mod binary_heap;
#[cfg(feature = "defmt-impl")]
mod defmt;
#[cfg(all(has_cas, feature = "cas"))]
pub mod mpmc;
#[cfg(all(has_cas, feature = "cas"))]
pub mod pool;
pub mod sorted_linked_list;
#[cfg(has_atomics)]
pub mod spsc;

#[cfg(feature = "ufmt-impl")]
mod ufmt;

mod sealed;

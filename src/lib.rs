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
//! static mut XS: Vec<u8, U8> = Vec::new();
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
//! Out Of Memory (OOM) condition (which defaults to abort) while performing operations
//! on them. It's certainly possible to run out of capacity while growing `heapless` data
//! structures, but the API lets you handle this possibility by returning a `Result` on operations
//! that may exhaust the capacity of the data structure.
//!
//! List of currently implemented data structures:
//!
//! - [`BinaryHeap`] -- priority queue
//! - [`IndexMap`] -- hash table
//! - [`IndexSet`] -- hash set
//! - [`LinearMap`]
//! - [`ObjectPool`] -- an object / memory pool
//! - [`RingBuffer`] -- single producer single consumer lockless queue
//! - [`String`]
//! - [`Vec`](struct.Vec.html)

#![allow(warnings)]
#![deny(missing_docs)]
#![deny(warnings)]
#![feature(const_fn)]
#![feature(core_intrinsics)]
#![feature(nonzero)]
#![feature(untagged_unions)]
#![no_std]

extern crate generic_array;
extern crate hash32;
extern crate stable_deref_trait;
#[cfg(test)]
extern crate std;

pub use binary_heap::BinaryHeap;
pub use generic_array::typenum::consts;
pub use generic_array::{ArrayLength, GenericArray};
pub use indexmap::{FnvIndexMap, IndexMap};
pub use indexset::{FnvIndexSet, IndexSet};
pub use linear_map::LinearMap;
pub use object_pool::ObjectPool;
pub use ring_buffer::RingBuffer;
#[doc(hidden)]
pub use stable_deref_trait::StableDeref;
pub use string::String;
pub use vec::Vec;

mod cfail;
mod indexmap;
mod indexset;
mod linear_map;
mod string;
mod vec;

#[doc(hidden)]
pub mod __core;
pub mod binary_heap;
pub mod object_pool;
pub mod ring_buffer;

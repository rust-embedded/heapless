//! `static` friendly data structures that don't require dynamic memory allocation
//!
//! Currently implemented data structures:
//!
//! - [`BinaryHeap`](binary_heap/struct.BinaryHeap.html)
//! - [`LinearMap`](struct.LinearMap.html)
//! - [`RingBuffer`](ring_buffer/struct.RingBuffer.html)
//! - [`String`](struct.String.html)
//! - [`Vec`](struct.Vec.html)

#![deny(missing_docs)]
#![deny(warnings)]
#![feature(const_fn)]
#![feature(core_intrinsics)]
#![feature(unsize)]
#![no_std]

#[cfg(test)]
extern crate std;
extern crate untagged_option;

pub use binary_heap::BinaryHeap;
pub use linear_map::LinearMap;
pub use ring_buffer::RingBuffer;
pub use string::String;
pub use vec::Vec;

mod cfail;
mod linear_map;
mod string;
mod vec;

pub mod binary_heap;
pub mod ring_buffer;

/// Error raised when the buffer is full
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BufferFullError;

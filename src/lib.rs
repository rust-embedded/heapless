//! `static` friendly data structures that don't require dynamic memory
//! allocation

#![deny(missing_docs)]
#![deny(warnings)]
#![feature(const_fn)]
#![no_std]

mod vec;
pub use vec::Vec;

mod circular_buffer;
pub use circular_buffer::CircularBuffer;

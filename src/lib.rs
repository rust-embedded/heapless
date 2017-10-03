//! `static` friendly data structures that don't require dynamic memory
//! allocation

#![feature(const_fn)]
#![feature(shared)]
#![feature(unsize)]
#![no_std]

extern crate untagged_option;

pub use vec::Vec;
pub use ring_buffer::RingBuffer;

pub mod ring_buffer;
mod vec;

/// Error
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Error {
    Full,
}

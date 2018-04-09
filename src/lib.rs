//! `static` friendly data structures that don't require dynamic memory allocation
//!
//! # Examples
//!
//! ## `Vec`
//!
//! ```
//! use heapless::Vec;
//!
//! let mut xs: Vec<u8, [u8; 4]> = Vec::new();
//!
//! assert!(xs.push(0).is_ok());
//! assert!(xs.push(1).is_ok());
//! assert!(xs.push(2).is_ok());
//! assert!(xs.push(3).is_ok());
//! assert!(xs.push(4).is_err()); // full
//!
//! assert_eq!(xs.pop(), Some(3));
//! ```
//!
//! ## `String`
//!
//! ```
//! use std::fmt::Write;
//!
//! use heapless::String;
//!
//! let mut s = String::<[u8; 8]>::new();
//!
//! write!(s, "hello").unwrap();
//!
//! assert_eq!(s.as_bytes(), b"hello");
//! ```
//!
//! ## `LinearMap`
//!
//! ```
//! use heapless::LinearMap;
//!
//! let mut map: LinearMap<_, _, [_; 8]> = LinearMap::new();
//!
//! map.insert("a", 1);
//! map.insert("b", 2);
//! map.insert("c", 3);
//!
//! assert_eq!(map["a"], 1);
//!
//! map["b"] += 1;
//! assert_eq!(map["b"], 3);
//!
//! map.remove("c");
//! assert_eq!(map.len(), 2);
//! ```
//!
//! ## `RingBuffer`
//!
//! ```
//! use heapless::RingBuffer;
//!
//! let mut rb: RingBuffer<u8, [u8; 4]> = RingBuffer::new();
//!
//! assert!(rb.enqueue(0).is_ok());
//! assert!(rb.enqueue(1).is_ok());
//! assert!(rb.enqueue(2).is_ok());
//! assert!(rb.enqueue(3).is_err()); // full
//!
//! assert_eq!(rb.dequeue(), Some(0));
//! ```
//!
//! ### Single producer single consumer mode
//!
//! ```
//! use heapless::RingBuffer;
//!
//! static mut RB: RingBuffer<Event, [Event; 4]> = RingBuffer::new();
//!
//! enum Event { A, B }
//!
//! fn main() {
//!     // NOTE(unsafe) beware of aliasing the `consumer` end point
//!     let mut consumer = unsafe { RB.split().1 };
//!
//!     loop {
//!         // `dequeue` is a lockless operation
//!         match consumer.dequeue() {
//!             Some(Event::A) => { /* .. */ },
//!             Some(Event::B) => { /* .. */ },
//!             None => { /* sleep */},
//!         }
//! #       break
//!     }
//! }
//!
//! // this is a different execution context that can preempt `main`
//! fn interrupt_handler() {
//!     // NOTE(unsafe) beware of aliasing the `producer` end point
//!     let mut producer = unsafe { RB.split().0 };
//! #   let condition = true;
//!
//!     // ..
//!
//!     if condition {
//!         producer.enqueue(Event::A).unwrap();
//!     } else {
//!         producer.enqueue(Event::B).unwrap();
//!     }
//!
//!     // ..
//! }
//! ```

#![deny(missing_docs)]
#![deny(warnings)]
#![allow(stable_features)]
#![feature(const_fn)]
#![feature(core_intrinsics)]
#![feature(conservative_impl_trait)]
#![feature(unsize)]
#![no_std]

extern crate untagged_option;

pub use linear_map::LinearMap;
pub use ring_buffer::RingBuffer;
pub use string::String;
pub use vec::Vec;

mod linear_map;
mod cfail;
mod string;
mod vec;
pub mod ring_buffer;

/// Error raised when the buffer is full
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BufferFullError;

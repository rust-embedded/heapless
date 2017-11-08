//! `static` friendly data structures that don't require dynamic memory
//! allocation
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
//! For use in *single core* systems like microcontrollers
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
//!
//! # `Send`-ness
//!
//! Collections of `Send`-able things are `Send`
//!
//! ```
//! use heapless::{RingBuffer, Vec};
//! use heapless::ring_buffer::{Consumer, Producer};
//!
//! struct IsSend;
//!
//! unsafe impl Send for IsSend {}
//!
//! fn is_send<T>() where T: Send {}
//!
//! is_send::<Consumer<IsSend, [IsSend; 4]>>();
//! is_send::<Producer<IsSend, [IsSend; 4]>>();
//! is_send::<RingBuffer<IsSend, [IsSend; 4]>>();
//! is_send::<Vec<IsSend, [IsSend; 4]>>();
//! ```
//!
//! Collections of not `Send`-able things are *not* `Send`
//!
//! ``` compile_fail
//! use std::marker::PhantomData;
//! use heapless::ring_buffer::Consumer;
//!
//! type NotSend = PhantomData<*const ()>;
//!
//! fn is_send<T>() where T: Send {}
//!
//! is_send::<Consumer<NotSend, [NotSend; 4]>>();
//! ```
//!
//! ``` compile_fail
//! use std::marker::PhantomData;
//! use heapless::ring_buffer::Producer;
//!
//! type NotSend = PhantomData<*const ()>;
//!
//! fn is_send<T>() where T: Send {}
//!
//! is_send::<Producer<NotSend, [NotSend; 4]>>();
//! ```
//!
//! ``` compile_fail
//! use std::marker::PhantomData;
//! use heapless::RingBuffer;
//!
//! type NotSend = PhantomData<*const ()>;
//!
//! fn is_send<T>() where T: Send {}
//!
//! is_send::<RingBuffer<NotSend, [NotSend; 4]>>();
//! ```
//!
//! ``` compile_fail
//! use std::marker::PhantomData;
//! use heapless::Vec;
//!
//! type NotSend = PhantomData<*const ()>;
//!
//! fn is_send<T>() where T: Send {}
//!
//! is_send::<Vec<NotSend, [NotSend; 4]>>();
//! ```

#![deny(missing_docs)]
#![feature(const_fn)]
#![feature(const_unsafe_cell_new)]
#![feature(core_intrinsics)]
#![feature(shared)]
#![feature(unsize)]
#![no_std]

extern crate untagged_option;

pub use vec::Vec;
pub use ring_buffer::RingBuffer;

pub mod ring_buffer;
mod vec;

/// Error raised when the buffer is full
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BufferFullError;

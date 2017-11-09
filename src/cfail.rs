//! Compile fail tests
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
//! Collections of non-`Send`-able things are *not* `Send`
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
//!
//! # Freeze
//!
//! Splitting a `RingBuffer` should invalidate the original reference.
//!
//! ``` compile_fail
//! use heapless::RingBuffer;
//!
//! let mut rb: RingBuffer<u8, [u8; 4]> = RingBuffer::new();
//!
//! let (p, c) = rb.split();
//! rb.enqueue(0).unwrap();
//! ```

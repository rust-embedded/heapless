//! A fixed capacity multiple-producer, multiple-consumer (MPMC) lock-free queue.
//!
//! **Note:** This module requires atomic compare-and-swap (CAS) instructions. On
//! targets where they're not natively available, they are emulated by the
//! [`portable-atomic`](https://crates.io/crates/portable-atomic) crate.
//!
//! # Example
//!
//! This queue can be constructed in `const` context. Placing it in a `static` variable lets *all*
//! contexts (interrupts/threads/`main`) safely enqueue and dequeue items.
//!
//! ```
//! use core::sync::atomic::{AtomicU8, Ordering};
//!
//! use heapless::mpmc::Queue;
//!
//! static Q: Queue<u8, 2> = Queue::new();
//!
//! fn main() {
//!     // Configure systick interrupt.
//!
//!     loop {
//!         if let Some(x) = Q.dequeue() {
//!             println!("{}", x);
//!         } else {
//!             // Wait for interrupt.
//!         }
//! #       break
//!     }
//! }
//!
//! fn systick() {
//!     static COUNT: AtomicU8 = AtomicU8::new(0);
//!     let count = COUNT.fetch_add(1, Ordering::SeqCst);
//!
//! #   let _ =
//!     Q.enqueue(count);
//! }
//! ```
//!
//! # Benchmark
//!
//! Measured on an ARM Cortex-M3 core running at 8 MHz and with zero flash wait cycles, compiled with `-C opt-level=z`:
//!
//! | Method                      | Time | N  |
//! |:----------------------------|-----:|---:|
//! | `Queue::<u8, 8>::enqueue()` |   34 |  0 |
//! | `Queue::<u8, 8>::enqueue()` |   52 |  1 |
//! | `Queue::<u8, 8>::enqueue()` |   69 |  2 |
//! | `Queue::<u8, 8>::dequeue()` |   35 |  0 |
//! | `Queue::<u8, 8>::dequeue()` |   53 |  1 |
//! | `Queue::<u8, 8>::dequeue()` |   71 |  2 |
//!
//! - N denotes the number of interruptions. On Cortex-M, an interruption consists of an
//!   interrupt handler preempting the would-be atomic section of the `enqueue`/`dequeue`
//!   operation. Note that it does *not* matter if the higher priority handler uses the queue or
//!   not.
//! - All execution times are in clock cycles (1 clock cycle = 125 ns).
//! - Execution time is *dependent* on `mem::size_of::<T>()`, as both operations include
//!   `ptr::read::<T>()` or `ptr::write::<T>()` in their successful path.
//! - The numbers reported correspond to the successful path, i.e. `dequeue` returning `Some`
//!   and `enqueue` returning `Ok`.
//!
//! # References
//!
//! This is an implementation of Dmitry Vyukov's [bounded MPMC queue], minus the
//! cache padding.
//!
//! [bounded MPMC queue]: http://www.1024cores.net/home/lock-free-algorithms/queues/bounded-mpmc-queue

#[cfg(feature = "mpmc_crossbeam")]
pub mod crossbeam_array_queue;
#[cfg(feature = "mpmc_crossbeam")]
pub use crossbeam_array_queue::*;

#[cfg(not(feature = "mpmc_crossbeam"))]
mod original;
#[cfg(not(feature = "mpmc_crossbeam"))]
pub use original::*;

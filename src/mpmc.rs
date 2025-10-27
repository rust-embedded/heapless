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
//!
//! <div class="warning">
//!
//! This implementation is not fully lock-free. If a thread or task gets preempted during
//! a `dequeue` or `enqueue` operation, it may prevent other operations from succeeding until
//! it's scheduled again to finish its operation.
//!
//! See <https://github.com/rust-embedded/heapless/issues/583> for more details.
//!
//! </div>
//! # References
//!
//! This is an implementation of Dmitry Vyukov's [bounded MPMC queue], minus the
//! cache padding.
//!
//! [bounded MPMC queue]: http://www.1024cores.net/home/lock-free-algorithms/queues/bounded-mpmc-queue

#[cfg(loom)]
use loom::sync::atomic;

#[cfg(not(any(feature = "portable-atomic", loom)))]
use core::sync::atomic;
#[cfg(all(feature = "portable-atomic", not(loom)))]
use portable_atomic as atomic;

use crate::storage::ViewStorage;

#[cfg(feature = "mpmc_large")]
type AtomicTargetSize = atomic::AtomicUsize;
#[cfg(not(feature = "mpmc_large"))]
type AtomicTargetSize = atomic::AtomicU8;

#[cfg(feature = "mpmc_large")]
type UintSize = usize;
#[cfg(not(feature = "mpmc_large"))]
type UintSize = u8;

#[cfg(feature = "mpmc_large")]
#[allow(unused)]
type IntSize = isize;
#[cfg(not(feature = "mpmc_large"))]
#[allow(unused)]
type IntSize = i8;

#[cfg(all(not(feature = "mpmc_nblfq"), not(feature = "mpmc_crossbeam")))]
mod original;
#[cfg(all(not(feature = "mpmc_nblfq"), not(feature = "mpmc_crossbeam")))]
pub use original::*;

#[cfg(feature = "mpmc_crossbeam")]
mod crossbeam_array_queue;
#[cfg(feature = "mpmc_crossbeam")]
pub use crossbeam_array_queue::*;

#[cfg(all(feature = "mpmc_nblfq", not(feature = "mpmc_crossbeam")))]
mod nblfq;
#[cfg(all(feature = "mpmc_nblfq", not(feature = "mpmc_crossbeam")))]
pub use nblfq::*;

/// A [`Queue`] with dynamic capacity.
///
/// [`Queue`] coerces to `QueueView`. `QueueView` is `!Sized`, meaning it can only ever be used by reference.
pub type QueueView<T> = QueueInner<T, ViewStorage>;

#[cfg(not(loom))]
#[cfg(test)]
mod tests {
    use static_assertions::assert_not_impl_any;

    use super::Queue;

    const N: usize = 4;

    // Ensure a `Queue` containing `!Send` values stays `!Send` itself.
    assert_not_impl_any!(Queue<*const (), 4>: Send);

    #[test]
    fn memory_leak() {
        droppable!();

        let q = Queue::<_, 2>::new();
        q.enqueue(Droppable::new()).unwrap_or_else(|_| panic!());
        q.enqueue(Droppable::new()).unwrap_or_else(|_| panic!());
        drop(q);

        assert_eq!(Droppable::count(), 0);
    }

    #[test]
    fn sanity() {
        let q = Queue::<_, 2>::new();
        q.enqueue(0).unwrap();
        q.enqueue(1).unwrap();
        assert!(q.enqueue(2).is_err());

        assert_eq!(q.dequeue(), Some(0));
        assert_eq!(q.dequeue(), Some(1));
        assert_eq!(q.dequeue(), None);
    }

    #[test]
    fn drain_at_pos255() {
        let q = Queue::<_, 2>::new();
        for _ in 0..255 {
            assert!(q.enqueue(0).is_ok());
            assert_eq!(q.dequeue(), Some(0));
        }

        // Queue is empty, this should not block forever.
        assert_eq!(q.dequeue(), None);
    }

    #[test]
    fn full_at_wrapped_pos0() {
        let q = Queue::<_, 2>::new();
        for _ in 0..254 {
            assert!(q.enqueue(0).is_ok());
            assert_eq!(q.dequeue(), Some(0));
        }
        assert!(q.enqueue(0).is_ok());
        assert!(q.enqueue(0).is_ok());
        // this should not block forever
        assert!(q.enqueue(0).is_err());
    }

    #[test]
    fn enqueue_full() {
        #[cfg(not(feature = "mpmc_large"))]
        const CAPACITY: usize = 128;

        #[cfg(feature = "mpmc_large")]
        const CAPACITY: usize = 256;

        let q: Queue<u8, CAPACITY> = Queue::new();

        assert_eq!(q.capacity(), CAPACITY);

        for _ in 0..CAPACITY {
            q.enqueue(0xAA).unwrap();
        }

        // Queue is full, this should not block forever.
        q.enqueue(0x55).unwrap_err();
    }

    #[test]
    fn test_enqueue_contention_rt() {
        use thread_priority::*;

        let q0 = std::sync::Arc::new(Queue::<u8, N>::new());

        for i in 0..N {
            q0.enqueue(i as u8).expect("new enqueue");
        }

        let model_thread = |q0: std::sync::Arc<Queue<u8, N>>| {
            for k in 0..N {
                match q0.dequeue() {
                    Some(_i) => (),
                    None if q0.is_empty() => (),
                    None => panic!(
                        "enqueue: Dequeue failed on iteration: {k}, empty queue?: {}, queue len: {}",
                        q0.is_empty(),
                        q0.len()
                    ),
                };

                q0.enqueue(k as u8).unwrap();
            }
        };

        let q1 = q0.clone();
        let h1 = ThreadBuilder::default()
            .name("h1")
            .priority(ThreadPriority::Max)
            .policy(ThreadSchedulePolicy::Realtime(
                RealtimeThreadSchedulePolicy::Fifo,
            ))
            .spawn(move |_| model_thread(q1))
            .unwrap();

        let q2 = q0.clone();
        let h2 = ThreadBuilder::default()
            .name("h2")
            .priority(ThreadPriority::Max)
            .policy(ThreadSchedulePolicy::Realtime(
                RealtimeThreadSchedulePolicy::Fifo,
            ))
            .spawn(move |_| model_thread(q2))
            .unwrap();

        h1.join().unwrap();
        h2.join().unwrap();
    }

    #[test]
    fn test_dequeue_contention_rt() {
        use thread_priority::*;

        let q0 = std::sync::Arc::new(Queue::<u8, N>::new());

        let model_thread = |q0: std::sync::Arc<Queue<u8, N>>| {
            for k in 0..N {
                q0.enqueue(k as u8).unwrap();
                match q0.dequeue() {
                    Some(_i) => (),
                    None if q0.is_empty() => (),
                    None => {
                        panic!(
                            "dequeue: Dequeue failed on iteration: {k}, queue is empty?: {}, queue len: {}",
                            q0.is_empty(),
                            q0.len()
                        );
                    }
                }
            }
        };

        let q1 = q0.clone();
        let h1 = ThreadBuilder::default()
            .name("h1")
            .priority(ThreadPriority::Max)
            .policy(ThreadSchedulePolicy::Realtime(
                RealtimeThreadSchedulePolicy::Fifo,
            ))
            .spawn(move |_| model_thread(q1))
            .unwrap();

        let q2 = q0.clone();
        let h2 = ThreadBuilder::default()
            .name("h2")
            .priority(ThreadPriority::Max)
            .policy(ThreadSchedulePolicy::Realtime(
                RealtimeThreadSchedulePolicy::Fifo,
            ))
            .spawn(move |_| model_thread(q2))
            .unwrap();

        h1.join().unwrap();
        h2.join().unwrap();
    }

    #[test]
    fn test_issue_583_enqueue_rt() {
        use thread_priority::*;

        fn to_vec<T>(q: &Queue<T, N>) -> Vec<T> {
            // inaccurate
            let mut ret = vec![];
            while let Some(v) = q.dequeue() {
                ret.push(v);
            }
            ret
        }

        let q0 = std::sync::Arc::new(Queue::<u8, N>::new());

        let model_thread = move |q0: std::sync::Arc<Queue<u8, N>>| {
            for k in 0..1_000_000 {
                if let Some(v) = q0.dequeue() {
                    q0.enqueue(v)
                        .unwrap_or_else(|v| panic!("{}: q0 -> q0: {}, {:?}", k, v, to_vec(&q0)));
                }
            }
        };

        let q1 = q0.clone();
        let h1 = ThreadBuilder::default()
            .name("h1")
            .priority(ThreadPriority::Max)
            .policy(ThreadSchedulePolicy::Realtime(
                RealtimeThreadSchedulePolicy::Fifo,
            ))
            .spawn(move |_| model_thread(q1))
            .unwrap();

        let q2 = q0.clone();
        let h2 = ThreadBuilder::default()
            .name("h2")
            .priority(ThreadPriority::Max)
            .policy(ThreadSchedulePolicy::Realtime(
                RealtimeThreadSchedulePolicy::Fifo,
            ))
            .spawn(move |_| model_thread(q2))
            .unwrap();

        h1.join().unwrap();
        h2.join().unwrap();
    }
}

#[cfg(all(loom, test))]
mod tests_loom {
    use super::*;
    use std::sync::Arc;
    const N: usize = 4;

    #[test]
    #[cfg(loom)]
    fn loom_issue_583_enqueue() {
        loom::model(|| {
            let q0 = Arc::new(Queue::<u8, N>::new());
            q0.enqueue(0).unwrap();
            q0.enqueue(1).unwrap();
            q0.enqueue(2).unwrap();
            q0.enqueue(3).unwrap();
            let model_thread = || {
                let q0 = q0.clone();
                move || {
                    for k in 0..10 {
                        let Some(i) = q0.dequeue() else {
                            panic!("{k}");
                        };
                        if q0.enqueue(k as u8).is_err() {
                            panic!("{i}");
                        }
                    }
                }
            };

            let h1 = loom::thread::spawn(model_thread());
            let h2 = loom::thread::spawn(model_thread());
            h1.join().unwrap();
            h2.join().unwrap();
        });
    }

    #[test]
    #[cfg(loom)]
    fn loom_issue_583_dequeue() {
        loom::model(|| {
            let q0 = Arc::new(Queue::<u8, N>::new());
            let model_thread = || {
                let q0 = q0.clone();
                move || {
                    for k in 0..10 {
                        q0.enqueue(k as u8).unwrap();
                        if q0.dequeue().is_none() {
                            panic!("{k}");
                        }
                    }
                }
            };

            let h1 = loom::thread::spawn(model_thread());
            let h2 = loom::thread::spawn(model_thread());
            h1.join().unwrap();
            h2.join().unwrap();
        });
    }
}

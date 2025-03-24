//! A fixed capacity Multiple-Producer Multiple-Consumer (MPMC) lock-free queue.
//!
//! NOTE: This module requires atomic CAS operations. On targets where they're not natively available,
//! they are emulated by the [`portable-atomic`](https://crates.io/crates/portable-atomic) crate.
//!
//! # Example
//!
//! This queue can be constructed in "const context". Placing it in a `static` variable lets *all*
//! contexts (interrupts/threads/`main`) safely enqueue and dequeue items from it.
//!
//! ``` ignore
//! #![no_main]
//! #![no_std]
//!
//! use panic_semihosting as _;
//!
//! use cortex_m::{asm, peripheral::syst::SystClkSource};
//! use cortex_m_rt::{entry, exception};
//! use cortex_m_semihosting::hprintln;
//! use heapless::mpmc::Q2;
//!
//! static Q: Q2<u8> = Q2::new();
//!
//! #[entry]
//! fn main() -> ! {
//!     if let Some(p) = cortex_m::Peripherals::take() {
//!         let mut syst = p.SYST;
//!
//!         // configures the system timer to trigger a SysTick exception every second
//!         syst.set_clock_source(SystClkSource::Core);
//!         syst.set_reload(12_000_000);
//!         syst.enable_counter();
//!         syst.enable_interrupt();
//!     }
//!
//!     loop {
//!         if let Some(x) = Q.dequeue() {
//!             hprintln!("{}", x).ok();
//!         } else {
//!             asm::wfi();
//!         }
//!     }
//! }
//!
//! #[exception]
//! fn SysTick() {
//!     static mut COUNT: u8 = 0;
//!
//!     Q.enqueue(*COUNT).ok();
//!     *COUNT += 1;
//! }
//! ```
//!
//! # Benchmark
//!
//! Measured on a ARM Cortex-M3 core running at 8 MHz and with zero Flash wait cycles
//!
//! N| `Q8::<u8>::enqueue().ok()` (`z`) | `Q8::<u8>::dequeue()` (`z`) |
//! -|----------------------------------|-----------------------------|
//! 0|34                                |35                           |
//! 1|52                                |53                           |
//! 2|69                                |71                           |
//!
//! - `N` denotes the number of *interruptions*. On Cortex-M, an interruption consists of an
//!   interrupt handler preempting the would-be atomic section of the `enqueue`/`dequeue`
//!   operation. Note that it does *not* matter if the higher priority handler uses the queue or
//!   not.
//! - All execution times are in clock cycles. 1 clock cycle = 125 ns.
//! - Execution time is *dependent* of `mem::size_of::<T>()`. Both operations include one
//!   `memcpy(T)` in their successful path.
//! - The optimization level is indicated in parentheses.
//! - The numbers reported correspond to the successful path (i.e. `Some` is returned by `dequeue`
//!   and `Ok` is returned by `enqueue`).
//!
//! # Portability
//!
//! This module requires CAS atomic instructions which are not available on all architectures
//! (e.g.  ARMv6-M (`thumbv6m-none-eabi`) and MSP430 (`msp430-none-elf`)). These atomics can be
//! emulated however with [`portable-atomic`](https://crates.io/crates/portable-atomic), which is
//! enabled with the `cas` feature and is enabled by default for `thumbv6m-none-eabi` and `riscv32`
//! targets.
//!
//! # References
//!
//! This is an implementation of Dmitry Vyukov's ["Bounded MPMC queue"][0] minus the cache padding.
//!
//! [0]: http://www.1024cores.net/home/lock-free-algorithms/queues/bounded-mpmc-queue

use core::{cell::UnsafeCell, mem::MaybeUninit};

#[cfg(not(feature = "portable-atomic"))]
use core::sync::atomic;
#[cfg(feature = "portable-atomic")]
use portable_atomic as atomic;

use atomic::Ordering;

use crate::storage::{OwnedStorage, Storage, ViewStorage};

#[cfg(feature = "mpmc_large")]
type AtomicTargetSize = atomic::AtomicUsize;
#[cfg(not(feature = "mpmc_large"))]
type AtomicTargetSize = atomic::AtomicU8;

#[cfg(feature = "mpmc_large")]
type UintSize = usize;
#[cfg(not(feature = "mpmc_large"))]
type UintSize = u8;

#[cfg(feature = "mpmc_large")]
type IntSize = isize;
#[cfg(not(feature = "mpmc_large"))]
type IntSize = i8;

/// MPMC queue with a capability for 2 elements.
pub type Q2<T> = MpMcQueue<T, 2>;

/// MPMC queue with a capability for 4 elements.
pub type Q4<T> = MpMcQueue<T, 4>;

/// MPMC queue with a capability for 8 elements.
pub type Q8<T> = MpMcQueue<T, 8>;

/// MPMC queue with a capability for 16 elements.
pub type Q16<T> = MpMcQueue<T, 16>;

/// MPMC queue with a capability for 32 elements.
pub type Q32<T> = MpMcQueue<T, 32>;

/// MPMC queue with a capability for 64 elements.
pub type Q64<T> = MpMcQueue<T, 64>;

/// Base struct for [`MpMcQueue`] and [`MpMcQueueView`], generic over the [`Storage`].
///
/// In most cases you should use [`MpMcQueue`] or [`MpMcQueueView`] directly. Only use this
/// struct if you want to write code that's generic over both.
pub struct MpMcQueueInner<T, S: Storage> {
    dequeue_pos: AtomicTargetSize,
    enqueue_pos: AtomicTargetSize,
    buffer: UnsafeCell<S::Buffer<Cell<T>>>,
}

/// MPMC queue with a capacity for N elements
/// N must be a power of 2
/// The max value of N is `u8::MAX` - 1 if `mpmc_large` feature is not enabled.
pub type MpMcQueue<T, const N: usize> = MpMcQueueInner<T, OwnedStorage<N>>;

/// MPMC queue with a capacity for N elements
/// N must be a power of 2
/// The max value of N is `u8::MAX` - 1 if `mpmc_large` feature is not enabled.
pub type MpMcQueueView<T> = MpMcQueueInner<T, ViewStorage>;

impl<T, const N: usize> MpMcQueue<T, N> {
    /// Creates an empty queue
    pub const fn new() -> Self {
        const {
            assert!(N > 1);
            assert!(N.is_power_of_two());
            assert!(N < UintSize::MAX as usize);
        }

        let mut cell_count = 0;

        let mut result_cells: [Cell<T>; N] = [const { Cell::new(0) }; N];
        while cell_count != N {
            result_cells[cell_count] = Cell::new(cell_count);
            cell_count += 1;
        }

        Self {
            buffer: UnsafeCell::new(result_cells),
            dequeue_pos: AtomicTargetSize::new(0),
            enqueue_pos: AtomicTargetSize::new(0),
        }
    }
    /// Get a reference to the `MpMcQueue`, erasing the `N` const-generic.
    ///
    ///
    /// ```rust
    /// # use heapless::mpmc::{MpMcQueue, MpMcQueueView};
    /// let queue: MpMcQueue<u8, 2> = MpMcQueue::new();
    /// let view: &MpMcQueueView<u8> = queue.as_view();
    /// ```
    ///
    /// It is often preferable to do the same through type coerction, since `MpMcQueue<T, N>` implements `Unsize<MpMcQueueView<T>>`:
    ///
    /// ```rust
    /// # use heapless::mpmc::{MpMcQueue, MpMcQueueView};
    /// let queue: MpMcQueue<u8, 2> = MpMcQueue::new();
    /// let view: &MpMcQueueView<u8> = &queue;
    /// ```
    #[inline]
    pub const fn as_view(&self) -> &MpMcQueueView<T> {
        self
    }

    /// Get a mutable reference to the `MpMcQueue`, erasing the `N` const-generic.
    ///
    /// ```rust
    /// # use heapless::mpmc::{MpMcQueue, MpMcQueueView};
    /// let mut queue: MpMcQueue<u8, 2> = MpMcQueue::new();
    /// let view: &mut MpMcQueueView<u8> = queue.as_mut_view();
    /// ```
    ///
    /// It is often preferable to do the same through type coerction, since `MpMcQueue<T, N>` implements `Unsize<MpMcQueueView<T>>`:
    ///
    /// ```rust
    /// # use heapless::mpmc::{MpMcQueue, MpMcQueueView};
    /// let mut queue: MpMcQueue<u8, 2> = MpMcQueue::new();
    /// let view: &mut MpMcQueueView<u8> = &mut queue;
    /// ```
    #[inline]
    pub fn as_mut_view(&mut self) -> &mut MpMcQueueView<T> {
        self
    }
}

impl<T, S: Storage> MpMcQueueInner<T, S> {
    fn mask(&self) -> UintSize {
        (S::len(self.buffer.get()) - 1) as _
    }

    /// Returns the item in the front of the queue, or `None` if the queue is empty
    pub fn dequeue(&self) -> Option<T> {
        unsafe { dequeue(S::as_ptr(self.buffer.get()), &self.dequeue_pos, self.mask()) }
    }

    /// Adds an `item` to the end of the queue
    ///
    /// Returns back the `item` if the queue is full
    pub fn enqueue(&self, item: T) -> Result<(), T> {
        unsafe {
            enqueue(
                S::as_ptr(self.buffer.get()),
                &self.enqueue_pos,
                self.mask(),
                item,
            )
        }
    }
}

impl<T, const N: usize> Default for MpMcQueue<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, S: Storage> Drop for MpMcQueueInner<T, S> {
    fn drop(&mut self) {
        // drop all contents currently in the queue
        while self.dequeue().is_some() {}
    }
}

unsafe impl<T, S: Storage> Sync for MpMcQueueInner<T, S> where T: Send {}

struct Cell<T> {
    data: MaybeUninit<T>,
    sequence: AtomicTargetSize,
}

impl<T> Cell<T> {
    const fn new(seq: usize) -> Self {
        Self {
            data: MaybeUninit::uninit(),
            sequence: AtomicTargetSize::new(seq as UintSize),
        }
    }
}

unsafe fn dequeue<T>(
    buffer: *mut Cell<T>,
    dequeue_pos: &AtomicTargetSize,
    mask: UintSize,
) -> Option<T> {
    let mut pos = dequeue_pos.load(Ordering::Relaxed);

    let mut cell;
    loop {
        cell = buffer.add(usize::from(pos & mask));
        let seq = (*cell).sequence.load(Ordering::Acquire);
        let dif = (seq as IntSize).wrapping_sub((pos.wrapping_add(1)) as IntSize);

        match dif.cmp(&0) {
            core::cmp::Ordering::Equal => {
                if dequeue_pos
                    .compare_exchange_weak(
                        pos,
                        pos.wrapping_add(1),
                        Ordering::Relaxed,
                        Ordering::Relaxed,
                    )
                    .is_ok()
                {
                    break;
                }
            }
            core::cmp::Ordering::Less => {
                return None;
            }
            core::cmp::Ordering::Greater => {
                pos = dequeue_pos.load(Ordering::Relaxed);
            }
        }
    }

    let data = (*cell).data.as_ptr().read();
    (*cell)
        .sequence
        .store(pos.wrapping_add(mask).wrapping_add(1), Ordering::Release);
    Some(data)
}

unsafe fn enqueue<T>(
    buffer: *mut Cell<T>,
    enqueue_pos: &AtomicTargetSize,
    mask: UintSize,
    item: T,
) -> Result<(), T> {
    let mut pos = enqueue_pos.load(Ordering::Relaxed);

    let mut cell;
    loop {
        cell = buffer.add(usize::from(pos & mask));
        let seq = (*cell).sequence.load(Ordering::Acquire);
        let dif = (seq as IntSize).wrapping_sub(pos as IntSize);

        match dif.cmp(&0) {
            core::cmp::Ordering::Equal => {
                if enqueue_pos
                    .compare_exchange_weak(
                        pos,
                        pos.wrapping_add(1),
                        Ordering::Relaxed,
                        Ordering::Relaxed,
                    )
                    .is_ok()
                {
                    break;
                }
            }
            core::cmp::Ordering::Less => {
                return Err(item);
            }
            core::cmp::Ordering::Greater => {
                pos = enqueue_pos.load(Ordering::Relaxed);
            }
        }
    }

    (*cell).data.as_mut_ptr().write(item);
    (*cell)
        .sequence
        .store(pos.wrapping_add(1), Ordering::Release);
    Ok(())
}

#[cfg(test)]
mod tests {
    use static_assertions::assert_not_impl_any;

    use super::{MpMcQueue, Q2};

    // Ensure a `MpMcQueue` containing `!Send` values stays `!Send` itself.
    assert_not_impl_any!(MpMcQueue<*const (), 4>: Send);

    #[test]
    fn memory_leak() {
        droppable!();

        let q = Q2::new();
        q.enqueue(Droppable::new()).unwrap_or_else(|_| panic!());
        q.enqueue(Droppable::new()).unwrap_or_else(|_| panic!());
        drop(q);

        assert_eq!(Droppable::count(), 0);
    }

    #[test]
    fn sanity() {
        let q = Q2::new();
        q.enqueue(0).unwrap();
        q.enqueue(1).unwrap();
        assert!(q.enqueue(2).is_err());

        assert_eq!(q.dequeue(), Some(0));
        assert_eq!(q.dequeue(), Some(1));
        assert_eq!(q.dequeue(), None);
    }

    #[test]
    fn drain_at_pos255() {
        let q = Q2::new();
        for _ in 0..255 {
            assert!(q.enqueue(0).is_ok());
            assert_eq!(q.dequeue(), Some(0));
        }

        // Queue is empty, this should not block forever.
        assert_eq!(q.dequeue(), None);
    }

    #[test]
    fn full_at_wrapped_pos0() {
        let q = Q2::new();
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

        let q: MpMcQueue<u8, CAPACITY> = MpMcQueue::new();

        for _ in 0..CAPACITY {
            q.enqueue(0xAA).unwrap();
        }

        // Queue is full, this should not block forever.
        q.enqueue(0x55).unwrap_err();
    }
}

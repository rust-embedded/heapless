//! A fixed capacity Multiple-Producer Multiple-Consumer (MPMC) lock-free queue
//!
//! # Example
//!
//! This queue can be constructed in "const context". Placing it in a `static` variable lets *all*
//! contexts (interrupts / threads / `main`) safely enqueue and dequeue items from it.
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
//!   interrupt handler preempting the would-be atomic section of the `enqueue` / `dequeue`
//!   operation. Note that it does *not* matter if the higher priority handler uses the queue or
//!   not.
//! - All execution times are in clock cycles. 1 clock cycle = 125 ns.
//! - Execution time is *dependent* of `mem::size_of::<T>()`. Both operations include one
//! `memcpy(T)` in their successful path.
//! - The optimization level is indicated in parentheses.
//! - The numbers reported correspond to the successful path (i.e. `Some` is returned by `dequeue`
//! and `Ok` is returned by `enqueue`).
//!
//! # Portability
//!
//! This module is not exposed to architectures that lack the instructions to implement CAS loops.
//! Those architectures include ARMv6-M (`thumbv6m-none-eabi`) and MSP430 (`msp430-none-elf`).
//!
//! # References
//!
//! This is an implementation of Dmitry Vyukov's ["Bounded MPMC queue"][0] minus the cache padding.
//!
//! [0]: http://www.1024cores.net/home/lock-free-algorithms/queues/bounded-mpmc-queue

use core::{
    cell::UnsafeCell,
    mem::MaybeUninit,
    sync::atomic::{AtomicU8, Ordering},
};

/// MPMC queue with a capacity for 2 elements
pub struct Q2<T> {
    buffer: UnsafeCell<[Cell<T>; 2]>,
    dequeue_pos: AtomicU8,
    enqueue_pos: AtomicU8,
}

impl<T> Q2<T> {
    const MASK: u8 = 2 - 1;

    /// Creates an empty queue
    pub const fn new() -> Self {
        Self {
            buffer: UnsafeCell::new([Cell::new(0), Cell::new(1)]),
            dequeue_pos: AtomicU8::new(0),
            enqueue_pos: AtomicU8::new(0),
        }
    }

    /// Returns the item in the front of the queue, or `None` if the queue is empty
    pub fn dequeue(&self) -> Option<T> {
        unsafe { dequeue(self.buffer.get() as *mut _, &self.dequeue_pos, Self::MASK) }
    }

    /// Adds an `item` to the end of the queue
    ///
    /// Returns back the `item` if the queue is full
    pub fn enqueue(&self, item: T) -> Result<(), T> {
        unsafe {
            enqueue(
                self.buffer.get() as *mut _,
                &self.enqueue_pos,
                Self::MASK,
                item,
            )
        }
    }
}

unsafe impl<T> Sync for Q2<T> where T: Send {}

/// MPMC queue with a capacity for 4 elements
pub struct Q4<T> {
    buffer: UnsafeCell<[Cell<T>; 4]>,
    dequeue_pos: AtomicU8,
    enqueue_pos: AtomicU8,
}

impl<T> Q4<T> {
    const MASK: u8 = 4 - 1;

    /// Creates an empty queue
    pub const fn new() -> Self {
        Self {
            buffer: UnsafeCell::new([Cell::new(0), Cell::new(1), Cell::new(2), Cell::new(3)]),
            dequeue_pos: AtomicU8::new(0),
            enqueue_pos: AtomicU8::new(0),
        }
    }

    /// Returns the item in the front of the queue, or `None` if the queue is empty
    pub fn dequeue(&self) -> Option<T> {
        unsafe { dequeue(self.buffer.get() as *mut _, &self.dequeue_pos, Self::MASK) }
    }

    /// Adds an `item` to the end of the queue
    ///
    /// Returns back the `item` if the queue is full
    pub fn enqueue(&self, item: T) -> Result<(), T> {
        unsafe {
            enqueue(
                self.buffer.get() as *mut _,
                &self.enqueue_pos,
                Self::MASK,
                item,
            )
        }
    }
}

unsafe impl<T> Sync for Q4<T> where T: Send {}

/// MPMC queue with a capacity for 8 elements
pub struct Q8<T> {
    buffer: UnsafeCell<[Cell<T>; 8]>,
    dequeue_pos: AtomicU8,
    enqueue_pos: AtomicU8,
}

impl<T> Q8<T> {
    const MASK: u8 = 8 - 1;

    /// Creates an empty queue
    pub const fn new() -> Self {
        Self {
            buffer: UnsafeCell::new([
                Cell::new(0),
                Cell::new(1),
                Cell::new(2),
                Cell::new(3),
                Cell::new(4),
                Cell::new(5),
                Cell::new(6),
                Cell::new(7),
            ]),
            dequeue_pos: AtomicU8::new(0),
            enqueue_pos: AtomicU8::new(0),
        }
    }

    /// Returns the item in the front of the queue, or `None` if the queue is empty
    pub fn dequeue(&self) -> Option<T> {
        unsafe { dequeue(self.buffer.get() as *mut _, &self.dequeue_pos, Self::MASK) }
    }

    /// Adds an `item` to the end of the queue
    ///
    /// Returns back the `item` if the queue is full
    pub fn enqueue(&self, item: T) -> Result<(), T> {
        unsafe {
            enqueue(
                self.buffer.get() as *mut _,
                &self.enqueue_pos,
                Self::MASK,
                item,
            )
        }
    }
}

unsafe impl<T> Sync for Q8<T> where T: Send {}

/// MPMC queue with a capacity for 16 elements
pub struct Q16<T> {
    buffer: UnsafeCell<[Cell<T>; 16]>,
    dequeue_pos: AtomicU8,
    enqueue_pos: AtomicU8,
}

impl<T> Q16<T> {
    const MASK: u8 = 16 - 1;

    /// Creates an empty queue
    pub const fn new() -> Self {
        Self {
            buffer: UnsafeCell::new([
                Cell::new(0),
                Cell::new(1),
                Cell::new(2),
                Cell::new(3),
                Cell::new(4),
                Cell::new(5),
                Cell::new(6),
                Cell::new(7),
                Cell::new(8),
                Cell::new(9),
                Cell::new(10),
                Cell::new(11),
                Cell::new(12),
                Cell::new(13),
                Cell::new(14),
                Cell::new(15),
            ]),
            dequeue_pos: AtomicU8::new(0),
            enqueue_pos: AtomicU8::new(0),
        }
    }

    /// Returns the item in the front of the queue, or `None` if the queue is empty
    pub fn dequeue(&self) -> Option<T> {
        unsafe { dequeue(self.buffer.get() as *mut _, &self.dequeue_pos, Self::MASK) }
    }

    /// Adds an `item` to the end of the queue
    ///
    /// Returns back the `item` if the queue is full
    pub fn enqueue(&self, item: T) -> Result<(), T> {
        unsafe {
            enqueue(
                self.buffer.get() as *mut _,
                &self.enqueue_pos,
                Self::MASK,
                item,
            )
        }
    }
}

unsafe impl<T> Sync for Q16<T> where T: Send {}

/// MPMC queue with a capacity for 32 elements
pub struct Q32<T> {
    buffer: UnsafeCell<[Cell<T>; 32]>,
    dequeue_pos: AtomicU8,
    enqueue_pos: AtomicU8,
}

impl<T> Q32<T> {
    const MASK: u8 = 32 - 1;

    /// Creates an empty queue
    pub const fn new() -> Self {
        Self {
            buffer: UnsafeCell::new([
                Cell::new(0),
                Cell::new(1),
                Cell::new(2),
                Cell::new(3),
                Cell::new(4),
                Cell::new(5),
                Cell::new(6),
                Cell::new(7),
                Cell::new(8),
                Cell::new(9),
                Cell::new(10),
                Cell::new(11),
                Cell::new(12),
                Cell::new(13),
                Cell::new(14),
                Cell::new(15),
                Cell::new(16),
                Cell::new(17),
                Cell::new(18),
                Cell::new(19),
                Cell::new(20),
                Cell::new(21),
                Cell::new(22),
                Cell::new(23),
                Cell::new(24),
                Cell::new(25),
                Cell::new(26),
                Cell::new(27),
                Cell::new(28),
                Cell::new(29),
                Cell::new(30),
                Cell::new(31),
            ]),
            dequeue_pos: AtomicU8::new(0),
            enqueue_pos: AtomicU8::new(0),
        }
    }

    /// Returns the item in the front of the queue, or `None` if the queue is empty
    pub fn dequeue(&self) -> Option<T> {
        unsafe { dequeue(self.buffer.get() as *mut _, &self.dequeue_pos, Self::MASK) }
    }

    /// Adds an `item` to the end of the queue
    ///
    /// Returns back the `item` if the queue is full
    pub fn enqueue(&self, item: T) -> Result<(), T> {
        unsafe {
            enqueue(
                self.buffer.get() as *mut _,
                &self.enqueue_pos,
                Self::MASK,
                item,
            )
        }
    }
}

unsafe impl<T> Sync for Q32<T> where T: Send {}

/// MPMC queue with a capacity for 64 elements
pub struct Q64<T> {
    buffer: UnsafeCell<[Cell<T>; 64]>,
    dequeue_pos: AtomicU8,
    enqueue_pos: AtomicU8,
}

impl<T> Q64<T> {
    const MASK: u8 = 64 - 1;

    /// Creates an empty queue
    pub const fn new() -> Self {
        Self {
            buffer: UnsafeCell::new([
                Cell::new(0),
                Cell::new(1),
                Cell::new(2),
                Cell::new(3),
                Cell::new(4),
                Cell::new(5),
                Cell::new(6),
                Cell::new(7),
                Cell::new(8),
                Cell::new(9),
                Cell::new(10),
                Cell::new(11),
                Cell::new(12),
                Cell::new(13),
                Cell::new(14),
                Cell::new(15),
                Cell::new(16),
                Cell::new(17),
                Cell::new(18),
                Cell::new(19),
                Cell::new(20),
                Cell::new(21),
                Cell::new(22),
                Cell::new(23),
                Cell::new(24),
                Cell::new(25),
                Cell::new(26),
                Cell::new(27),
                Cell::new(28),
                Cell::new(29),
                Cell::new(30),
                Cell::new(31),
                Cell::new(32),
                Cell::new(33),
                Cell::new(34),
                Cell::new(35),
                Cell::new(36),
                Cell::new(37),
                Cell::new(38),
                Cell::new(39),
                Cell::new(40),
                Cell::new(41),
                Cell::new(42),
                Cell::new(43),
                Cell::new(44),
                Cell::new(45),
                Cell::new(46),
                Cell::new(47),
                Cell::new(48),
                Cell::new(49),
                Cell::new(50),
                Cell::new(51),
                Cell::new(52),
                Cell::new(53),
                Cell::new(54),
                Cell::new(55),
                Cell::new(56),
                Cell::new(57),
                Cell::new(58),
                Cell::new(59),
                Cell::new(60),
                Cell::new(61),
                Cell::new(62),
                Cell::new(63),
            ]),
            dequeue_pos: AtomicU8::new(0),
            enqueue_pos: AtomicU8::new(0),
        }
    }

    /// Returns the item in the front of the queue, or `None` if the queue is empty
    pub fn dequeue(&self) -> Option<T> {
        unsafe { dequeue(self.buffer.get() as *mut _, &self.dequeue_pos, Self::MASK) }
    }

    /// Adds an `item` to the end of the queue
    ///
    /// Returns back the `item` if the queue is full
    pub fn enqueue(&self, item: T) -> Result<(), T> {
        unsafe {
            enqueue(
                self.buffer.get() as *mut _,
                &self.enqueue_pos,
                Self::MASK,
                item,
            )
        }
    }
}

unsafe impl<T> Sync for Q64<T> where T: Send {}

struct Cell<T> {
    data: MaybeUninit<T>,
    sequence: AtomicU8,
}

impl<T> Cell<T> {
    const fn new(seq: u8) -> Self {
        Self {
            data: MaybeUninit::uninit(),
            sequence: AtomicU8::new(seq),
        }
    }
}

unsafe fn dequeue<T>(buffer: *mut Cell<T>, dequeue_pos: &AtomicU8, mask: u8) -> Option<T> {
    let mut pos = dequeue_pos.load(Ordering::Relaxed);

    let mut cell;
    loop {
        cell = buffer.add(usize::from(pos & mask));
        let seq = (*cell).sequence.load(Ordering::Acquire);
        let dif = i16::from(seq) - i16::from(pos.wrapping_add(1));

        if dif == 0 {
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
        } else if dif < 0 {
            return None;
        } else {
            pos = dequeue_pos.load(Ordering::Relaxed);
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
    enqueue_pos: &AtomicU8,
    mask: u8,
    item: T,
) -> Result<(), T> {
    let mut pos = enqueue_pos.load(Ordering::Relaxed);

    let mut cell;
    loop {
        cell = buffer.add(usize::from(pos & mask));
        let seq = (*cell).sequence.load(Ordering::Acquire);
        let dif = i16::from(seq) - i16::from(pos);

        if dif == 0 {
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
        } else if dif < 0 {
            return Err(item);
        } else {
            pos = enqueue_pos.load(Ordering::Relaxed);
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
    use super::Q2;

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
}

/// Sealed traits and implementations for `spsc`
pub mod spsc {

use core::sync::atomic::{self, AtomicU16, AtomicU8, AtomicUsize, Ordering};
use crate::spsc::{MultiCore, SingleCore};

pub unsafe trait XCore {
    fn is_multi_core() -> bool;
}

unsafe impl XCore for SingleCore {
    fn is_multi_core() -> bool {
        false
    }
}

unsafe impl XCore for MultiCore {
    fn is_multi_core() -> bool {
        true
    }
}

pub unsafe trait Uxx: Into<usize> + Send {
    #[doc(hidden)]
    fn truncate(x: usize) -> Self;

    #[doc(hidden)]
    unsafe fn load_acquire<C>(x: *const Self) -> Self
    where
        C: XCore;

    #[doc(hidden)]
    fn load_relaxed(x: *const Self) -> Self;

    #[doc(hidden)]
    unsafe fn store_release<C>(x: *const Self, val: Self)
    where
        C: XCore;
}

unsafe impl Uxx for u8 {
    fn truncate(x: usize) -> Self {
        let max = ::core::u8::MAX;
        if x >= usize::from(max) {
            max
        } else {
            x as u8
        }
    }

    unsafe fn load_acquire<C>(x: *const Self) -> Self
    where
        C: XCore,
    {
        if C::is_multi_core() {
            (*(x as *const AtomicU8)).load(Ordering::Acquire)
        } else {
            let y = (*(x as *const AtomicU8)).load(Ordering::Relaxed); // read
            atomic::compiler_fence(Ordering::Acquire); // ▼
            y
        }
    }

    fn load_relaxed(x: *const Self) -> Self {
        unsafe { (*(x as *const AtomicU8)).load(Ordering::Relaxed) }
    }

    unsafe fn store_release<C>(x: *const Self, val: Self)
    where
        C: XCore,
    {
        if C::is_multi_core() {
            (*(x as *const AtomicU8)).store(val, Ordering::Release)
        } else {
            atomic::compiler_fence(Ordering::Release); // ▲
            (*(x as *const AtomicU8)).store(val, Ordering::Relaxed) // write
        }
    }
}

unsafe impl Uxx for u16 {
    fn truncate(x: usize) -> Self {
        let max = ::core::u16::MAX;
        if x >= usize::from(max) {
            max
        } else {
            x as u16
        }
    }

    unsafe fn load_acquire<C>(x: *const Self) -> Self
    where
        C: XCore,
    {
        if C::is_multi_core() {
            (*(x as *const AtomicU16)).load(Ordering::Acquire)
        } else {
            let y = (*(x as *const AtomicU16)).load(Ordering::Relaxed); // read
            atomic::compiler_fence(Ordering::Acquire); // ▼
            y
        }
    }

    fn load_relaxed(x: *const Self) -> Self {
        unsafe { (*(x as *const AtomicU16)).load(Ordering::Relaxed) }
    }

    unsafe fn store_release<C>(x: *const Self, val: Self)
    where
        C: XCore,
    {
        if C::is_multi_core() {
            (*(x as *const AtomicU16)).store(val, Ordering::Release)
        } else {
            atomic::compiler_fence(Ordering::Release); // ▲
            (*(x as *const AtomicU16)).store(val, Ordering::Relaxed) // write
        }
    }
}

unsafe impl Uxx for usize {
    fn truncate(x: usize) -> Self {
        x
    }

    unsafe fn load_acquire<C>(x: *const Self) -> Self
    where
        C: XCore,
    {
        if C::is_multi_core() {
            (*(x as *const AtomicUsize)).load(Ordering::Acquire)
        } else {
            let y = (*(x as *const AtomicUsize)).load(Ordering::Relaxed); // read
            atomic::compiler_fence(Ordering::Acquire); // ▼
            y
        }
    }

    fn load_relaxed(x: *const Self) -> Self {
        unsafe { (*(x as *const AtomicUsize)).load(Ordering::Relaxed) }
    }

    unsafe fn store_release<C>(x: *const Self, val: Self)
    where
        C: XCore,
    {
        if C::is_multi_core() {
            (*(x as *const AtomicUsize)).store(val, Ordering::Release)
        } else {
            atomic::compiler_fence(Ordering::Release); // ▲
            (*(x as *const AtomicUsize)).store(val, Ordering::Relaxed); // write
        }
    }
}

}

/// Sealed traits and implementations for `binary_heap`
pub mod binary_heap {

use core::cmp::Ordering;
use crate::binary_heap::{Min, Max};

/// The binary heap kind: min-heap or max-heap
pub unsafe trait Kind {
    #[doc(hidden)]
    fn ordering() -> Ordering;
}

unsafe impl Kind for Min {
    fn ordering() -> Ordering {
        Ordering::Less
    }
}

unsafe impl Kind for Max {
    fn ordering() -> Ordering {
        Ordering::Greater
    }
}

}

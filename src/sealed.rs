#[cfg(feature = "smaller-atomics")]
use core::sync::atomic::{AtomicU16, AtomicU8};
use core::sync::atomic::{AtomicUsize, Ordering};

pub unsafe trait Uxx: Into<usize> + Send {
    #[doc(hidden)]
    fn truncate(x: usize) -> Self;

    #[doc(hidden)]
    fn load_acquire(x: *const Self) -> Self;

    #[doc(hidden)]
    fn load_relaxed(x: *const Self) -> Self;

    #[doc(hidden)]
    fn store_release(x: *const Self, val: Self);
}

#[cfg(feature = "smaller-atomics")]
unsafe impl Uxx for u8 {
    fn truncate(x: usize) -> Self {
        let max = ::core::u8::MAX;
        if x >= usize::from(max) {
            max
        } else {
            x as u8
        }
    }

    fn load_acquire(x: *const Self) -> Self {
        unsafe { (*(x as *const AtomicU8)).load(Ordering::Acquire) }
    }

    fn load_relaxed(x: *const Self) -> Self {
        unsafe { (*(x as *const AtomicU8)).load(Ordering::Relaxed) }
    }

    fn store_release(x: *const Self, val: Self) {
        unsafe { (*(x as *const AtomicU8)).store(val, Ordering::Relaxed) }
    }
}

#[cfg(feature = "smaller-atomics")]
unsafe impl Uxx for u16 {
    fn truncate(x: usize) -> Self {
        let max = ::core::u16::MAX;
        if x >= usize::from(max) {
            max
        } else {
            x as u16
        }
    }

    fn load_acquire(x: *const Self) -> Self {
        unsafe { (*(x as *const AtomicU16)).load(Ordering::Acquire) }
    }

    fn load_relaxed(x: *const Self) -> Self {
        unsafe { (*(x as *const AtomicU16)).load(Ordering::Relaxed) }
    }

    fn store_release(x: *const Self, val: Self) {
        unsafe { (*(x as *const AtomicU16)).store(val, Ordering::Relaxed) }
    }
}

unsafe impl Uxx for usize {
    fn truncate(x: usize) -> Self {
        x
    }

    fn load_acquire(x: *const Self) -> Self {
        unsafe { (*(x as *const AtomicUsize)).load(Ordering::Acquire) }
    }

    fn load_relaxed(x: *const Self) -> Self {
        unsafe { (*(x as *const AtomicUsize)).load(Ordering::Relaxed) }
    }

    fn store_release(x: *const Self, val: Self) {
        unsafe { (*(x as *const AtomicUsize)).store(val, Ordering::Relaxed) }
    }
}

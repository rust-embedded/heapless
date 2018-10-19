#[cfg(not(feature = "smaller-atomics"))]
use core::sync::atomic::{AtomicUsize, Ordering};

pub unsafe trait Uxx: Into<usize> + Send {
    #[doc(hidden)]
    fn truncate(x: usize) -> Self;

    #[cfg(feature = "smaller-atomics")]
    #[doc(hidden)]
    fn load_acquire(x: *mut Self) -> Self {
        unsafe { core::intrinsics::atomic_load_acq(x) }
    }

    #[cfg(not(feature = "smaller-atomics"))]
    #[doc(hidden)]
    fn load_acquire(x: *mut Self) -> Self;

    #[cfg(feature = "smaller-atomics")]
    #[doc(hidden)]
    fn load_relaxed(x: *mut Self) -> Self {
        unsafe { core::intrinsics::atomic_load_relaxed(x) }
    }

    #[cfg(not(feature = "smaller-atomics"))]
    #[doc(hidden)]
    fn load_relaxed(x: *mut Self) -> Self;

    #[cfg(feature = "smaller-atomics")]
    #[doc(hidden)]
    fn store_release(x: *mut Self, val: Self) {
        unsafe { core::intrinsics::atomic_store_rel(x, val) }
    }

    #[cfg(not(feature = "smaller-atomics"))]
    #[doc(hidden)]
    fn store_release(x: *mut Self, val: Self);
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
}

unsafe impl Uxx for usize {
    fn truncate(x: usize) -> Self {
        x
    }

    #[cfg(not(feature = "smaller-atomics"))]
    fn load_acquire(x: *mut Self) -> Self {
        unsafe { (*(x as *mut AtomicUsize)).load(Ordering::Acquire) }
    }

    #[cfg(not(feature = "smaller-atomics"))]
    fn load_relaxed(x: *mut Self) -> Self {
        unsafe { (*(x as *mut AtomicUsize)).load(Ordering::Relaxed) }
    }

    #[cfg(not(feature = "smaller-atomics"))]
    fn store_release(x: *mut Self, val: Self) {
        unsafe {
            (*(x as *mut AtomicUsize)).store(val, Ordering::Release);
        }
    }
}

/// Sealed traits and implementations for `spsc`
pub mod spsc {
    #[cfg(has_atomics)]
    use crate::spsc::{MultiCore, SingleCore};
    #[cfg(has_atomics)]
    use core::sync::atomic::{self, AtomicU16, AtomicU8, AtomicUsize, Ordering};

    pub unsafe trait XCore {
        fn is_multi_core() -> bool;
    }

    #[cfg(has_atomics)]
    unsafe impl XCore for SingleCore {
        fn is_multi_core() -> bool {
            false
        }
    }

    #[cfg(has_atomics)]
    unsafe impl XCore for MultiCore {
        fn is_multi_core() -> bool {
            true
        }
    }

    pub unsafe trait Uxx: Into<usize> + Send {
        #[doc(hidden)]
        fn saturate(x: usize) -> Self;

        #[doc(hidden)]
        fn truncate(x: usize) -> Self;

        #[cfg(has_atomics)]
        #[doc(hidden)]
        unsafe fn load_acquire<C>(x: *const Self) -> Self
        where
            C: XCore;

        #[cfg(has_atomics)]
        #[doc(hidden)]
        fn load_relaxed(x: *const Self) -> Self;

        #[cfg(has_atomics)]
        #[doc(hidden)]
        unsafe fn store_release<C>(x: *const Self, val: Self)
        where
            C: XCore;
    }

    unsafe impl Uxx for u8 {
        fn saturate(x: usize) -> Self {
            let max = Self::max_value() as usize;
            if x >= usize::from(max) {
                max as Self
            } else {
                x as Self
            }
        }

        fn truncate(x: usize) -> Self {
            x as Self
        }

        #[cfg(has_atomics)]
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

        #[cfg(has_atomics)]
        fn load_relaxed(x: *const Self) -> Self {
            unsafe { (*(x as *const AtomicU8)).load(Ordering::Relaxed) }
        }

        #[cfg(has_atomics)]
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
        fn saturate(x: usize) -> Self {
            let max = Self::max_value() as usize;
            if x >= usize::from(max) {
                max as Self
            } else {
                x as Self
            }
        }

        fn truncate(x: usize) -> Self {
            x as Self
        }

        #[cfg(has_atomics)]
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

        #[cfg(has_atomics)]
        fn load_relaxed(x: *const Self) -> Self {
            unsafe { (*(x as *const AtomicU16)).load(Ordering::Relaxed) }
        }

        #[cfg(has_atomics)]
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
        fn saturate(x: usize) -> Self {
            x
        }

        fn truncate(x: usize) -> Self {
            x
        }

        #[cfg(has_atomics)]
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

        #[cfg(has_atomics)]
        fn load_relaxed(x: *const Self) -> Self {
            unsafe { (*(x as *const AtomicUsize)).load(Ordering::Relaxed) }
        }

        #[cfg(has_atomics)]
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
    use crate::binary_heap::{Max, Min};
    use core::cmp::Ordering;

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

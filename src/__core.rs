/// Temporary fork of some stuff in `core` that's doesn't have a `const fn` API

pub mod mem {
    #[cfg(not(feature = "const-fn"))]
    pub use core::mem;
    pub use core::mem::{replace, zeroed, ManuallyDrop};

    // See RFC 1892
    #[cfg(feature = "const-fn")]
    pub union MaybeUninit<T> {
        uninit: (),
        value: ManuallyDrop<T>,
    }

    // workaround to get this to compile on stable ("unions with non-`Copy` fields are unstable")
    #[cfg(not(feature = "const-fn"))]
    pub struct MaybeUninit<T> {
        value: ManuallyDrop<T>,
    }

    impl<T> MaybeUninit<T> {
        #[cfg(feature = "const-fn")]
        pub const unsafe fn uninitialized() -> Self {
            MaybeUninit { uninit: () }
        }

        #[cfg(not(feature = "const-fn"))]
        pub unsafe fn uninitialized() -> Self {
            MaybeUninit {
                value: ManuallyDrop::new(mem::uninitialized()),
            }
        }

        /// Get a reference to the contained value.
        ///
        /// # Unsafety
        ///
        /// It is up to the caller to guarantee that the the `MaybeUninit` really is in an
        /// initialized state, otherwise this will immediately cause undefined behavior.
        pub unsafe fn get_ref(&self) -> &T {
            &*self.value
        }

        /// Get a mutable reference to the contained value.
        ///
        /// # Unsafety
        ///
        /// It is up to the caller to guarantee that the the `MaybeUninit` really is in an
        /// initialized state, otherwise this will immediately cause undefined behavior.
        pub unsafe fn get_mut(&mut self) -> &mut T {
            &mut *self.value
        }
    }
}

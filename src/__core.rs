/// Temporary fork of some stuff in `core` that's doesn't have a `const fn` API

pub mod mem {
    pub use core::mem::{replace, zeroed, ManuallyDrop};
    use core::ops::{Deref, DerefMut};


    /// extremely unsafe uniniatilized memory
    /// only use with ManuallyDrop
    #[allow(unions_with_drop_fields)]
    pub(crate) union Uninit<T> {
        uninit: (),
        init: T,
    }

    impl<T> Uninit<T> {
        const_fn!(
            pub const unsafe fn new() -> Self {
                Uninit {
                    uninit: ()
                }
            }
        );
    }

    impl<T> Deref for Uninit<T> {
        type Target = T;
        fn deref(&self) -> &T {
            unsafe{ &self.init }
        }
    }

    impl<T> DerefMut for Uninit<T> {
        fn deref_mut(&mut self) -> &mut T {
            unsafe { &mut self.init }
        }
    }

}

#[cfg(feature = "const-fn")] // Remove this if there are more tests
#[cfg(test)]
mod test {
    use __core::mem::Uninit;
    use __core::mem::ManuallyDrop;
    use core;

    #[cfg(feature = "const-fn")]
    #[test]
    fn static_uninit() {
        static mut _I: Uninit<i32> = unsafe { Uninit::new() };
        unsafe {
            *_I = 42;
            assert_eq!(*_I, 42);
        }
    }

    #[cfg(feature = "const-fn")]
    #[test]
    fn static_new_manually_drop() {
        static mut M: ManuallyDrop<i32> = ManuallyDrop::new(42);
        unsafe {
            assert_eq!(*M, 42);
        }
        // Drop before deinitialization
        unsafe { core::ptr::drop_in_place(&mut M as &mut i32 as *mut i32) };
    }

}

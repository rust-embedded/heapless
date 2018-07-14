/// Temporary fork of some stuff in `core` that's doesn't have a `const fn` API

pub mod mem {
    #[cfg(not(feature = "const-fn"))]
    pub use core::mem::uninitialized;
    pub use core::mem::{replace, zeroed, ManuallyDrop};

    #[cfg(feature = "const-fn")]
    pub const unsafe fn uninitialized<T>() -> T {
        #[allow(unions_with_drop_fields)]
        union U<T> {
            none: (),
            some: T,
        }

        U { none: () }.some
    }
}

#[cfg(feature = "const-fn")] // Remove this if there are more tests
#[cfg(test)]
mod test {
    use __core;
    use __core::mem::ManuallyDrop;
    use core;

    #[cfg(feature = "const-fn")]
    #[test]
    fn static_uninitzialized() {
        static mut I: i32 = unsafe { __core::mem::uninitialized() };
        // Initialize before drop
        unsafe { core::ptr::write(&mut I as *mut i32, 42) };
        unsafe { assert_eq!(I, 42) };
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

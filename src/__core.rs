/// Temporary fork of some stuff in `core` that's doesn't have a `const fn` API

pub mod mem {
    pub use core::mem::{replace, zeroed};

    use core::ops::{Deref, DerefMut};

    #[allow(unions_with_drop_fields)]
    pub union ManuallyDrop<T> {
        value: T,
    }

    impl<T> ManuallyDrop<T> {
        #[inline]
        pub const fn new(value: T) -> ManuallyDrop<T> {
            ManuallyDrop { value: value }
        }
    }

    impl<T> Deref for ManuallyDrop<T> {
        type Target = T;

        #[inline]
        fn deref(&self) -> &Self::Target {
            unsafe { &self.value }
        }
    }

    impl<T> DerefMut for ManuallyDrop<T> {
        #[inline]
        fn deref_mut(&mut self) -> &mut Self::Target {
            unsafe { &mut self.value }
        }
    }

    pub const unsafe fn uninitialized<T>() -> T {
        #[allow(unions_with_drop_fields)]
        union U<T> {
            none: (),
            some: T,
        }

        U { none: () }.some
    }
}

macro_rules! droppable {
    () => {
        static COUNT: core::sync::atomic::AtomicI32 = core::sync::atomic::AtomicI32::new(0);
        static CREATED_COUNT: core::sync::atomic::AtomicI32 = core::sync::atomic::AtomicI32::new(0);

        #[derive(Eq, Ord, PartialEq, PartialOrd, Debug, Hash)]
        struct Droppable(i32, Box<i32>);
        impl Droppable {
            fn new() -> Self {
                COUNT.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
                Droppable(
                    CREATED_COUNT.fetch_add(1, core::sync::atomic::Ordering::Relaxed),
                    Box::new(0),
                )
            }

            #[allow(unused)]
            fn count() -> i32 {
                COUNT.load(core::sync::atomic::Ordering::Relaxed)
            }
        }
        impl Drop for Droppable {
            fn drop(&mut self) {
                // volatile to avoid the compiler optimizin away since the check can
                // only be reached through UB
                // SAFETY: we have a reference to self.1, this is a normal read
                let double_free_check = unsafe { core::ptr::read_volatile(&*self.1) };
                // SAFETY: we have a mut reference to self.1, this is a normal write
                unsafe {
                    core::ptr::write_volatile(&mut *self.1, self.0 + 1);
                }
                assert_eq!(double_free_check, 0, "Double free of {self:?}");
                let res = COUNT.fetch_sub(1, core::sync::atomic::Ordering::Relaxed);
                // res = 0 means that COUNT was 0 before the drop, therefore there is a double free
                assert!(res > 0);
            }
        }
    };
}

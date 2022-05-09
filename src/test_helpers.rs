macro_rules! droppable {
    () => {
        #[derive(Eq, Ord, PartialEq, PartialOrd)]
        struct Droppable(i32);
        impl Droppable {
            fn new() -> Self {
                unsafe {
                    COUNT += 1;
                    Droppable(COUNT)
                }
            }
        }
        impl Drop for Droppable {
            fn drop(&mut self) {
                unsafe {
                    COUNT -= 1;
                }
            }
        }

        static mut COUNT: i32 = 0;
    };
}

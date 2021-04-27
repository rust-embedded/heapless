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

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

/// Sealed traits and implementations for `LinkedList`
pub mod sorted_linked_list {
    use crate::sorted_linked_list::{Max, Min};
    use core::cmp::Ordering;

    /// The linked list kind: min-list or max-list
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

#[allow(dead_code)]
#[allow(path_statements)]
pub(crate) const fn smaller_than<const N: usize, const MAX: usize>() {
    Assert::<N, MAX>::LESS;
}

#[allow(dead_code)]
#[allow(path_statements)]
pub(crate) const fn greater_than_0<const N: usize>() {
    Assert::<N, 0>::GREATER;
}

#[allow(dead_code)]
#[allow(path_statements)]
pub(crate) const fn greater_than_1<const N: usize>() {
    Assert::<N, 1>::GREATER;
}

#[allow(dead_code)]
#[allow(path_statements)]
pub(crate) const fn power_of_two<const N: usize>() {
    Assert::<N, 0>::GREATER;
    Assert::<N, 0>::POWER_OF_TWO;
}

#[allow(dead_code)]
/// Const assert hack
pub struct Assert<const L: usize, const R: usize>;

#[allow(dead_code)]
impl<const L: usize, const R: usize> Assert<L, R> {
    /// Const assert hack
    pub const GREATER_EQ: usize = L - R;

    /// Const assert hack
    pub const LESS_EQ: usize = R - L;

    /// Const assert hack
    pub const NOT_EQ: isize = 0 / (R as isize - L as isize);

    /// Const assert hack
    pub const EQ: usize = (R - L) + (L - R);

    /// Const assert hack
    pub const GREATER: usize = L - R - 1;

    /// Const assert hack
    pub const LESS: usize = R - L - 1;

    /// Const assert hack
    pub const POWER_OF_TWO: usize = 0 - (L & (L - 1));
}

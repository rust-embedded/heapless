use core::{
    fmt::{Debug, Display},
    mem,
    ops::{Add, AddAssign, Sub, SubAssign},
};

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

pub trait Sealed:
    Send
    + Sync
    + Copy
    + Display
    + Debug
    + PartialEq
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
    + PartialOrd
    + TryFrom<usize, Error: Debug>
    + TryInto<usize, Error: Debug>
{
    /// The zero value of the integer type.
    const ZERO: Self;
    /// The one value of the integer type.
    const MAX: Self;
    /// The maximum value of this type, as a `usize`.
    const MAX_USIZE: usize;

    /// The one value of the integer type.
    ///
    /// It's a function instead of constant because we want to have implementation which panics for
    /// type `ZeroLenType`
    fn one() -> Self;

    /// An infallible conversion from `usize` to `LenT`.
    #[inline]
    fn from_usize(val: usize) -> Self {
        val.try_into().unwrap()
    }

    /// An infallible conversion from `LenT` to `usize`.
    #[inline]
    fn into_usize(self) -> usize {
        self.try_into().unwrap()
    }

    /// Converts `LenT` into `Some(usize)`, unless it's `Self::MAX`, where it returns `None`.
    #[inline]
    fn to_non_max(self) -> Option<usize> {
        if self == Self::MAX {
            None
        } else {
            Some(self.into_usize())
        }
    }
}

macro_rules! impl_lentype {
    ($($(#[$meta:meta])* $LenT:ty),*) => {$(
        $(#[$meta])*
        impl Sealed for $LenT {
            const ZERO: Self = 0;
            const MAX: Self = Self::MAX;
            const MAX_USIZE: usize = Self::MAX as _;

            fn one() -> Self {
                1
            }
        }

        $(#[$meta])*
        impl LenType for $LenT {}
    )*}
}

/// A sealed trait representing a valid type to use as a length for a container.
///
/// This cannot be implemented in user code, and is restricted to `u8`, `u16`, `u32`, and `usize`.
///
/// When the `zeroize` feature is enabled, this trait requires the `Zeroize` trait.
#[cfg(feature = "zeroize")]
pub trait LenType: Sealed + Zeroize {}

/// A sealed trait representing a valid type to use as a length for a container.
///
/// This cannot be implemented in user code, and is restricted to `u8`, `u16`, `u32`, and `usize`.
#[cfg(not(feature = "zeroize"))]
pub trait LenType: Sealed {}

impl_lentype!(
    u8,
    u16,
    #[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
    u32,
    usize
);

pub const fn check_capacity_fits<LenT: LenType, const N: usize>() {
    assert!(LenT::MAX_USIZE >= N, "The capacity is larger than `LenT` can hold, increase the size of `LenT` or reduce the capacity");
}

#[inline]
pub const fn to_len_type<L: LenType>(n: usize) -> L {
    try_to_len_type(n).unwrap()
}

#[inline]
pub const fn try_to_len_type<L: LenType>(n: usize) -> Option<L> {
    if n > L::MAX_USIZE {
        return None;
    }
    // The following "select" is safe, since we have fixed number of types
    // implementing LenType - all with distinctive size "signature".
    unsafe {
        // ALWAYS compiletime switch.
        Some(match size_of::<L>() {
            // transmute_copy, instead of transmute - because `L`
            // is a "dependent type".
            8 => mem::transmute_copy(&(n as u64)),
            4 => mem::transmute_copy(&(n as u32)),
            2 => mem::transmute_copy(&(n as u16)),
            1 => mem::transmute_copy(&(n as u8)),
            _ => unreachable!(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_len_cast() {
        const {
            assert!(to_len_type::<u16>(15000) == 15000);
        }
    }
}

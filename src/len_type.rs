use core::{
    fmt::{Debug, Display},
    mem,
    ops::{Add, AddAssign, BitAnd, Sub, SubAssign},
};

#[cfg(not(feature = "portable-atomic"))]
use core::sync::atomic::{AtomicU16, AtomicU32, AtomicU8, AtomicUsize, Ordering};
#[cfg(feature = "portable-atomic")]
use portable_atomic::{AtomicU16, AtomicU32, AtomicU8, AtomicUsize, Ordering};

#[allow(non_camel_case_types)]
pub enum TypeEnum {
    u8,
    u16,
    u32,
    usize,
}

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
    + BitAnd<Self, Output = Self>
    + Sub<Output = Self>
    + SubAssign
    + PartialOrd
    + Ord
    + TryFrom<usize, Error: Debug>
    + TryInto<usize, Error: Debug>
{
    /// The zero value of the integer type.
    const ZERO: Self;
    /// The one value of the integer type.
    const MAX: Self;
    /// The maximum value of this type, as a `usize`.
    const MAX_USIZE: usize;
    /// This type as an enum.
    const TYPE: TypeEnum;

    /// The corresponding atomic integer type.
    type Atomic: Atomic<Self, Self::Atomic>;
    /// The corresponding signed integer type.
    type Signed;

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

    /// Wrapping (modular) addition. Computes `self + rhs`, wrapping around at `Self::MAX_USIZE`.
    #[inline]
    fn wrapping_add(self, rhs: Self) -> Self {
        Self::from_usize(self.into_usize().wrapping_add(rhs.into_usize()) & Self::MAX_USIZE)
    }

    /// Compare `seq` and `expected_pos` as if they were signed integers, returning the result of
    /// `(seq as Signed).wrapping_sub(expected_pos as Signed).cmp(&0)`.
    #[inline]
    fn signed_wrapping_cmp(seq: Self, expected_pos: Self) -> core::cmp::Ordering {
        match seq.into_usize().wrapping_sub(expected_pos.into_usize()) {
            0 => core::cmp::Ordering::Equal,
            d if d > (Self::MAX_USIZE / 2) => core::cmp::Ordering::Less,
            _ => core::cmp::Ordering::Greater,
        }
    }
}

// TODO consider replacing with stdlib version once generic_atomic lands in stable
// (https://github.com/rust-lang/rust/issues/130539)
pub trait Atomic<T, A> {
    /// Loads a value from the atomic integer.
    ///
    /// Behavior must be identical to the corresponding `load` implementation for the underlying
    /// atomic type.
    fn load(&self, order: Ordering) -> T;
    /// Stores a value into the atomic integer.
    ///
    /// Behavior must be identical to the corresponding `store` implementation for the underlying
    /// atomic type.
    fn store(&self, val: T, order: Ordering);
    /// Stores a value into the atomic integer if the current value is the same as the current
    /// value.
    ///
    /// Behavior must be identical to the corresponding `compare_exchange_weak` implementation for
    /// the underlying atomic type.
    #[cfg(any(target_has_atomic = "ptr", feature = "portable-atomic"))]
    fn compare_exchange_weak(
        &self,
        current: T,
        new: T,
        success: Ordering,
        failure: Ordering,
    ) -> Result<T, T>;
}

macro_rules! impl_atomic {
    ($($(#[$meta:meta])* ($T:ty, $A:tt)),*) => {$(
        impl Atomic<$T, $A> for $A {
            fn load(&self, order: Ordering) -> $T {
                self.load(order)
            }
            fn store(&self, val: $T, order: Ordering) {
                self.store(val, order)
            }
            fn compare_exchange_weak(&self, current: $T, new: $T, success: Ordering, failure: Ordering) -> Result<$T, $T> {
                self.compare_exchange_weak(current, new, success, failure)
            }
        }
    )*}
}

/// Converts a `usize` into the atomic type associated with the given `LenType`.
pub const fn new_atomic_lentype<L: LenType>(val: usize) -> L::Atomic {
    unsafe {
        match L::TYPE {
            TypeEnum::u8 => mem::transmute_copy(&AtomicU8::new(val as u8)),
            TypeEnum::u16 => mem::transmute_copy(&AtomicU16::new(val as u16)),
            TypeEnum::u32 => mem::transmute_copy(&AtomicU32::new(val as u32)),
            TypeEnum::usize => mem::transmute_copy(&AtomicUsize::new(val)),
        }
    }
}

impl_atomic!(
    (u8, AtomicU8),
    (u16, AtomicU16),
    #[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
    (u32, AtomicU32),
    (usize, AtomicUsize)
);

macro_rules! impl_lentype {
    ($($(#[$meta:meta])* ($ULenT:tt, $SLenT:ty, $AULenT:ty)),*) => {$(
        $(#[$meta])*
        impl Sealed for $ULenT {
            const ZERO: Self = 0;
            const MAX: Self = Self::MAX;
            const MAX_USIZE: usize = Self::MAX as _;
            const TYPE: TypeEnum = TypeEnum::$ULenT;

            type Atomic = $AULenT;
            type Signed = $SLenT;

            fn one() -> Self {
                1
            }
        }

        $(#[$meta])*
        impl LenType for $ULenT {}
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
    (u8, i8, AtomicU8),
    (u16, i16, AtomicU16),
    #[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
    (u32, i32, AtomicU32),
    (usize, isize, AtomicUsize)
);

pub const fn check_capacity_fits<LenT: LenType, const N: usize>() {
    assert!(LenT::MAX_USIZE >= N, "The capacity is larger than `LenT` can hold, increase the size of `LenT` or reduce the capacity");
}

/// Const cast from [`usize`] to [`LenType`] with `as`.
#[inline]
pub const fn as_len_type<L: LenType>(n: usize) -> L {
    // SAFETY: transmute is safe since after cast we cast to the same type.
    unsafe {
        // ALWAYS compiletime switch.
        match L::TYPE {
            // transmute_copy, instead of transmute - because `L`
            // is a "dependent type".
            TypeEnum::u8 => mem::transmute_copy(&(n as u8)),
            TypeEnum::u16 => mem::transmute_copy(&(n as u16)),
            TypeEnum::u32 => mem::transmute_copy(&(n as u32)),
            TypeEnum::usize => mem::transmute_copy(&n),
        }
    }
}

/// Checked cast to [`LenType`].
///
/// # Panic
///
/// Panics if `n` is outside of `L` range.
#[inline]
pub const fn to_len_type<L: LenType>(n: usize) -> L {
    try_to_len_type(n).unwrap()
}

/// Checked cast to [`LenType`].
///
/// Returns `None` if `n` is outside of `L` range.
#[inline]
pub const fn try_to_len_type<L: LenType>(n: usize) -> Option<L> {
    if n > L::MAX_USIZE {
        return None;
    }
    Some(as_len_type(n))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_len_cast() {
        // 1. Check constness
        const {
            assert!(to_len_type::<u8>(150) == 150);
            assert!(to_len_type::<u16>(15_000) == 15_000);
            assert!(to_len_type::<u32>(1_500_000) == 1_500_000);
            assert!(to_len_type::<usize>(usize::MAX) == usize::MAX);
        }
        // 2. Check correctness
        fn check<T: LenType>() {
            const COUNT: usize = 100;
            for i in 0..COUNT {
                let n = i * (T::MAX_USIZE / COUNT);
                assert_eq!(to_len_type::<T>(n).into_usize(), n);
            }
        }
        check::<u8>();
        check::<u16>();
        check::<u32>();
        check::<usize>();
    }
}

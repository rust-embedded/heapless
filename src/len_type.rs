use core::{
    fmt::{Debug, Display},
    ops::{Add, AddAssign, Sub, SubAssign},
};

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
pub trait LenType: Sealed {}

impl_lentype!(
    u8,
    u16,
    #[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
    u32,
    usize
);

macro_rules! impl_lentodefault {
    ($LenT:ty: $($len:literal),*) => {$(
        impl SmallestLenType for Const<$len> {
            type Type = $LenT;
        }
    )*};
}

/// A struct to create individual types for mapping with [`SmallestLenType`].
///
/// See the documentation of [`DefaultLenType`] for a detailed explanation.
pub struct Const<const N: usize>;

/// A trait to map [`Const`] to it's respective [`LenType`].
///
/// See the documentation of [`DefaultLenType`] for a detailed explanation.
#[diagnostic::on_unimplemented(
    message = "Length `N` does not have a default `LenType` mapping",
    note = "Provide the `LenType` explicitly, such as `usize`"
)]
pub trait SmallestLenType {
    type Type: LenType;
}

/// A type alias to perform the `const N: usize` -> `LenType` mapping.
///
/// This is impossible to perform directly, but it is possible to write a `const N: usize` -> related `Type` mapping via a const generic argument,
/// then map from that to an unrelated type via a trait with associated types.
///
/// [`Const`] is the "related type" in the above explaination, [`SmallestLenType`] is the mapping trait.
#[allow(rustdoc::private_intra_doc_links)] // Only publically exposed via `crate::_export`
pub type DefaultLenType<const N: usize> = <Const<N> as SmallestLenType>::Type;

impl_lentodefault!(ZeroLenType: 0);
impl_lentodefault!(u8: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255);
impl_lentodefault!(u16: 256, 300, 400, 500, 512, 600, 700, 800, 900, 1000, 1024, 2000, 2048, 4000, 4096, 8000, 8192, 16000, 16384, 32000, 32768, 65000, 65535);
#[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
impl_lentodefault!(u32: 65536, 131072, 262144, 524288, 1048576, 2097152, 4194304, 8388608, 16777216, 33554432, 67108864, 134217728, 268435456, 536870912, 1073741824, 2147483648);

pub const fn check_capacity_fits<LenT: LenType, const N: usize>() {
    assert!(LenT::MAX_USIZE >= N, "The capacity is larger than `LenT` can hold, increase the size of `LenT` or reduce the capacity");
}

/// Container with 0 capacity always has length 0, so there is no need to track length of such containers at all.
///
/// This type is used as a placeholder for length of container with 0 capacity. It allows optimizing total size of
/// containers like this to 0 bytes.
///
/// Logically, this type always stores value 0. Because of this ZeroLenType::one() panics and should never be called.
#[doc(hidden)]
#[derive(Copy, Clone, PartialEq, PartialOrd)]
pub struct ZeroLenType;

impl Debug for ZeroLenType {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "0")
    }
}

impl Display for ZeroLenType {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "0")
    }
}

impl Sealed for ZeroLenType {
    const ZERO: Self = Self;

    const MAX: Self = Self;
    const MAX_USIZE: usize = 0;

    #[inline]
    fn one() -> Self {
        panic!("ZeroLenType cannot represent value 1");
    }
}

impl LenType for ZeroLenType {}

impl Add for ZeroLenType {
    type Output = Self;

    fn add(self, _rhs: Self) -> Self::Output {
        Self::ZERO
    }
}

impl AddAssign for ZeroLenType {
    fn add_assign(&mut self, _rhs: Self) {}
}

impl Sub for ZeroLenType {
    type Output = Self;

    fn sub(self, _rhs: Self) -> Self::Output {
        Self::ZERO
    }
}

impl SubAssign for ZeroLenType {
    fn sub_assign(&mut self, _rhs: Self) {}
}

#[doc(hidden)]
#[derive(Debug, PartialEq)]
pub struct ZeroLenTypeTryFromError;

impl TryFrom<usize> for ZeroLenType {
    type Error = ZeroLenTypeTryFromError;

    fn try_from(value: usize) -> Result<Self, Self::Error> {
        if value > 0 {
            return Err(ZeroLenTypeTryFromError);
        }

        Ok(Self::ZERO)
    }
}

impl TryInto<usize> for ZeroLenType {
    type Error = ();

    fn try_into(self) -> Result<usize, Self::Error> {
        Ok(0)
    }
}

#[cfg(test)]
mod tests {
    use crate::len_type::{Sealed, ZeroLenType, ZeroLenTypeTryFromError};

    #[test]
    pub fn test_zero_len_type_conversions() {
        assert_eq!(ZeroLenType::into_usize(ZeroLenType::ZERO), 0_usize);
        assert_eq!(ZeroLenType::from_usize(0_usize), ZeroLenType::ZERO);

        assert_eq!(ZeroLenType::ZERO.try_into(), Ok(0_usize));
        assert_eq!(ZeroLenType::try_from(0_usize), Ok(ZeroLenType::ZERO));
        assert_eq!(ZeroLenType::try_from(1_usize), Err(ZeroLenTypeTryFromError));
    }

    #[test]
    #[should_panic]
    pub fn test_zero_len_type_one() {
        ZeroLenType::one();
    }

    #[test]
    #[should_panic]
    pub fn test_zero_len_type_one_usize() {
        ZeroLenType::from_usize(1);
    }

    #[test]
    pub fn test_zero_len_type_constants() {
        assert_eq!(ZeroLenType::ZERO, ZeroLenType);
        assert_eq!(ZeroLenType::MAX, ZeroLenType);
        assert_eq!(ZeroLenType::MAX_USIZE, 0_usize);
    }

    #[test]
    pub fn test_zero_len_type_size() {
        assert_eq!(core::mem::size_of::<ZeroLenType>(), 0);
    }

    #[test]
    pub fn test_zero_len_type_ops() {
        assert_eq!(ZeroLenType::ZERO + ZeroLenType::ZERO, ZeroLenType::ZERO);
        assert_eq!(ZeroLenType::ZERO - ZeroLenType::ZERO, ZeroLenType::ZERO);

        let mut zero = ZeroLenType::ZERO;
        zero += ZeroLenType::ZERO;
        assert_eq!(zero, ZeroLenType::ZERO);
        zero -= ZeroLenType::ZERO;
        assert_eq!(zero, ZeroLenType::ZERO);
    }

    #[test]
    pub fn test_zero_len_type_debug() {
        assert_eq!(format!("{}", ZeroLenType), "0");
        assert_eq!(format!("{:?}", ZeroLenType), "0");
    }
}

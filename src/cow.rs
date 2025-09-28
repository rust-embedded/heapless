#![cfg(feature = "alloc")]

extern crate alloc;

use crate::len_type::LenType;
use crate::{CapacityError, String, StringView};
use core::borrow::Borrow;

/// A clone-on-write (COW) string type for heapless.
///
/// `Cow` can either **borrow** a `StringView` or **own** a `String`.
/// This allows efficient handling of strings that may be either temporary
/// references or fully owned data.
///
/// # Type Parameters
///
/// - `N`: The inline buffer size for owned strings.
/// - `LenT`: The integer type used for length tracking (must implement [`LenType`]).

/// A clone-on-write string type for heapless
#[derive(Debug)]
pub enum Cow<'a, const N: usize, LenT: LenType = usize> {
    /// A borrowed view of a string.
    Borrowed(&'a StringView<LenT>),

    /// An owned string with inline storage of size `N`.
    Owned(String<N, LenT>),
}

impl<'a, const N: usize, LenT: LenType> Cow<'a, N, LenT> {
    /// Converts the `Cow` into an owned [`String`].
    ///
    /// If the `Cow` is borrowed, this clones the underlying string data.
    /// If the `Cow` is already owned, this returns a clone of it.
    pub fn to_owned(&self) -> String<N, LenT> {
        match self {
            Cow::Borrowed(sv) => String::from(sv),
            Cow::Owned(s) => s.clone(),
        }
    }

    /// Returns the string as a `&str`.
    ///
    /// Works for both borrowed and owned variants.
    pub fn as_str(&self) -> &str {
        match self {
            Cow::Borrowed(sv) => sv.as_str(),
            Cow::Owned(s) => s.as_str(),
        }
    }

    /// Returns `true` if this `Cow` is a borrowed string.
    pub fn is_borrowed(&self) -> bool {
        matches!(self, Cow::Borrowed(_))
    }

    /// Returns `true` if this `Cow` is an owned string.
    pub fn is_owned(&self) -> bool {
        matches!(self, Cow::Owned(_))
    }
}

impl<'a, const N: usize, LenT: LenType> From<&'a StringView<LenT>> for Cow<'a, N, LenT> {
    /// Creates a borrowed `Cow` from a `StringView`.
    fn from(sv: &'a StringView<LenT>) -> Self {
        Cow::Borrowed(sv)
    }
}

impl<const N: usize, LenT: LenType> From<String<N, LenT>> for Cow<'_, N, LenT> {
    /// Creates an owned `Cow` from a `String`.
    fn from(s: String<N, LenT>) -> Self {
        Cow::Owned(s)
    }
}

impl<'a, const N: usize, LenT: LenType> Borrow<str> for Cow<'a, N, LenT> {
    /// Borrows the string as a `&str`.
    ///
    /// This allows `Cow` to be used anywhere a `&str` is expected.
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

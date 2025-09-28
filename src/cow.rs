#![cfg(feature = "alloc")]

extern crate alloc;

use crate::len_type::LenType;
use crate::{CapacityError, String, StringView};
use core::borrow::Borrow;

/// A clone-on-write string type for heapless
#[derive(Debug)]
pub enum Cow<'a, const N: usize, LenT: LenType = usize> {
    Borrowed(&'a StringView<LenT>),
    Owned(String<N, LenT>),
}

impl<'a, const N: usize, LenT: LenType> Cow<'a, N, LenT> {
    pub fn to_owned(&self) -> String<N, LenT> {
        match self {
            Cow::Borrowed(sv) => String::from(sv),
            Cow::Owned(s) => s.clone(),
        }
    }

    pub fn as_str(&self) -> &str {
        match self {
            Cow::Borrowed(sv) => sv.as_str(),
            Cow::Owned(s) => s.as_str(),
        }
    }

    pub fn is_borrowed(&self) -> bool {
        matches!(self, Cow::Borrowed(_))
    }

    pub fn is_owned(&self) -> bool {
        matches!(self, Cow::Owned(_))
    }
}

impl<'a, const N: usize, LenT: LenType> From<&'a StringView<LenT>> for Cow<'a, N, LenT> {
    fn from(sv: &'a StringView<LenT>) -> Self {
        Cow::Borrowed(sv)
    }
}

impl<const N: usize, LenT: LenType> From<String<N, LenT>> for Cow<'_, N, LenT> {
    fn from(s: String<N, LenT>) -> Self {
        Cow::Owned(s)
    }
}

impl<'a, const N: usize, LenT: LenType> Borrow<str> for Cow<'a, N, LenT> {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

//! Clone-on-write string type for heapless.
//! 
//! Provides `CowStr`, a heapless clone-on-write string that can be borrowed or owned.

use crate::len_type::LenType;
use crate::string::StringView;
use crate::String;
use core::borrow::Borrow;

/// A clone-on-write (COW) string type specialized for heapless strings.
///
/// `CowStr` can be either:
/// - `Borrowed(&'a StringView<LenT>)` for a non-`'static` borrowed view,
/// - `Static(&'static StringView<LenT>)` for a `'static` borrowed view,
/// - `Owned(String<N, LenT>)` for an owned heapless `String`.
#[derive(Debug, Clone)]
pub enum CowStr<'a, const N: usize, LenT: LenType = usize>
where
    LenT: 'static,
{
    /// A borrowed view with lifetime `'a`.
    Borrowed(&'a StringView<LenT>),
    /// A `'static` borrowed view.
    Static(&'static StringView<LenT>),
    /// An owned `String` with inline storage of size `N`.
    Owned(String<N, LenT>),
}

impl<'a, const N: usize, LenT: LenType> CowStr<'a, N, LenT>
where
    LenT: 'static,
{
    /// Convert the `CowStr` into an owned `String<N, LenT>`.
    ///
    /// Panics if the string does not fit in `N`.
    pub fn to_owned(&self) -> String<N, LenT> {
        match self {
            CowStr::Borrowed(sv) => String::try_from(sv.as_str())
                .expect("capacity too small for CowStr::to_owned"),
            CowStr::Static(sv) => String::try_from(sv.as_str())
                .expect("capacity too small for CowStr::to_owned"),
            CowStr::Owned(s) => s.clone(),
        }
    }

    /// Return the inner value as `&str`.
    pub fn as_str(&self) -> &str {
        match self {
            CowStr::Borrowed(sv) => sv.as_str(),
            CowStr::Static(sv) => sv.as_str(),
            CowStr::Owned(s) => s.as_str(),
        }
    }

    /// Is this a non-`'static` borrowed view?
    pub fn is_borrowed(&self) -> bool {
        matches!(self, CowStr::Borrowed(_))
    }

    /// Is this a `'static` borrowed view?
    pub fn is_static(&self) -> bool {
        matches!(self, CowStr::Static(_))
    }

    /// Is this an owned string?
    pub fn is_owned(&self) -> bool {
        matches!(self, CowStr::Owned(_))
    }
}

impl<'a, const N: usize, LenT: LenType> From<&'a StringView<LenT>> for CowStr<'a, N, LenT>
where
    LenT: 'static,
{
    fn from(sv: &'a StringView<LenT>) -> Self {
        CowStr::Borrowed(sv)
    }
}

impl<const N: usize, LenT: LenType> From<String<N, LenT>> for CowStr<'_, N, LenT>
where
    LenT: 'static,
{
    fn from(s: String<N, LenT>) -> Self {
        CowStr::Owned(s)
    }
}

impl<const N: usize, LenT: LenType> CowStr<'static, N, LenT>
where
    LenT: 'static,
{
    /// Construct a `CowStr` that holds a `'static` `StringView`.
    pub const fn from_static(sv: &'static StringView<LenT>) -> Self {
        CowStr::Static(sv)
    }
}

impl<'a, const N: usize, LenT: LenType> Borrow<str> for CowStr<'a, N, LenT>
where
    LenT: 'static,
{
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

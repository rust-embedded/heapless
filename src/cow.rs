//! Clone-on-write string type for heapless.
//!
//! Provides `CowStr`, a heapless clone-on-write string that can be
//! borrowed, static, or owned. Useful for efficiently handling
//! temporary string references and owned strings.
use crate::len_type::LenType;
use crate::string::StringView;
use crate::String;
use core::borrow::Borrow;

/// A clone-on-write (COW) string type specialized for heapless strings.
///
/// `CowStr` can be either:
/// - `Borrowed(&'a StringView<LenT>)` for a non-`'static` borrowed view,
/// - `Static(&'static StringView<LenT>)` for a `'static` borrowed view (no deep clone needed),
/// - `Owned(String<N, LenT>)` for an owned heapless `String`.
///
/// `N` is the inline buffer capacity; `LenT` is the length type (must implement [`LenType`]).
/// We add `LenT: 'static` because the `Static` variant stores `&'static StringView<LenT>`.
#[derive(Debug)]
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
    /// This uses `String::try_from(&str)` and will `panic!` on capacity overflow.
    pub fn to_owned(&self) -> String<N, LenT> {
        match self {
            CowStr::Borrowed(sv) => {
                String::try_from(sv.as_str()).expect("capacity too small for CowStr::to_owned")
            }
            CowStr::Static(sv) => {
                String::try_from(sv.as_str()).expect("capacity too small for CowStr::to_owned")
            }
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

// ---------------------- UNIT TESTS ----------------------
#[cfg(test)]
mod tests {
    use super::*;

    // Helper function to create a StringView from a static str
    fn sv_from_str(s: &'static str) -> StringView<usize> {
        StringView::new(s)
    }

    #[test]
    fn test_borrowed_variant() {
        let view = sv_from_str("hello");
        let cow: CowStr<16> = CowStr::Borrowed(&view);

        assert!(cow.is_borrowed());
        assert!(!cow.is_static());
        assert!(!cow.is_owned());
        assert_eq!(cow.as_str(), "hello");

        let owned = cow.to_owned();
        assert_eq!(owned.as_str(), "hello");
    }

    #[test]
    fn test_static_variant() {
        static VIEW: StringView<usize> = StringView::new("world");
        let cow: CowStr<16> = CowStr::from_static(&VIEW);

        assert!(!cow.is_borrowed());
        assert!(cow.is_static());
        assert!(!cow.is_owned());
        assert_eq!(cow.as_str(), "world");

        let owned = cow.to_owned();
        assert_eq!(owned.as_str(), "world");
    }

    #[test]
    fn test_owned_variant() {
        let s: String<16> = String::try_from("heapless").unwrap();
        let cow: CowStr<16> = CowStr::Owned(s.clone());

        assert!(!cow.is_borrowed());
        assert!(!cow.is_static());
        assert!(cow.is_owned());
        assert_eq!(cow.as_str(), "heapless");

        let owned = cow.to_owned();
        assert_eq!(owned.as_str(), "heapless");
    }

    #[test]
    fn test_from_stringview() {
        let view = sv_from_str("from_borrowed");
        let cow: CowStr<16> = CowStr::from(&view);

        assert!(cow.is_borrowed());
        assert_eq!(cow.as_str(), "from_borrowed");
    }

    #[test]
    fn test_from_string() {
        let s: String<16> = String::try_from("from_owned").unwrap();
        let cow: CowStr<16> = CowStr::from(s.clone());

        assert!(cow.is_owned());
        assert_eq!(cow.as_str(), "from_owned");
    }

    #[test]
    fn test_borrow_trait() {
        let s: String<16> = String::try_from("borrow_trait").unwrap();
        let cow: CowStr<16> = CowStr::Owned(s);

        let b: &str = cow.borrow();
        assert_eq!(b, "borrow_trait");
    }
}

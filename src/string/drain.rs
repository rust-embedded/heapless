use core::{fmt, iter::FusedIterator, str::Chars};

use super::StringView;

/// A draining iterator for `String`.
///
/// This struct is created by the [`drain`] method on [`crate::String`]. See its
/// documentation for more.
///
/// [`drain`]: crate::String::drain
pub struct Drain<'a> {
    /// Will be used as &'a mut String in the destructor
    pub(super) string: *mut StringView,
    /// Stast of part to remove
    pub(super) start: usize,
    /// End of part to remove
    pub(super) end: usize,
    /// Current remaining range to remove
    pub(super) iter: Chars<'a>,
}

impl fmt::Debug for Drain<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Drain").field(&self.as_str()).finish()
    }
}

unsafe impl Sync for Drain<'_> {}
unsafe impl Send for Drain<'_> {}

impl Drop for Drain<'_> {
    fn drop(&mut self) {
        unsafe {
            // Use `Vec::drain`. “Reaffirm” the bounds checks to avoid
            // panic code being inserted again.
            let self_vec = (*self.string).as_mut_vec();
            if self.start <= self.end && self.end <= self_vec.len() {
                self_vec.drain(self.start..self.end);
            }
        }
    }
}

impl<'a> Drain<'a> {
    /// Returns the remaining (sub)string of this iterator as a slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::String;
    ///
    /// let mut s = String::<8>::try_from("abc").unwrap();
    /// let mut drain = s.drain(..);
    /// assert_eq!(drain.as_str(), "abc");
    /// let _ = drain.next().unwrap();
    /// assert_eq!(drain.as_str(), "bc");
    /// ```
    #[must_use]
    pub fn as_str(&self) -> &str {
        self.iter.as_str()
    }
}

impl AsRef<str> for Drain<'_> {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsRef<[u8]> for Drain<'_> {
    fn as_ref(&self) -> &[u8] {
        self.as_str().as_bytes()
    }
}

impl Iterator for Drain<'_> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<char> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    #[inline]
    fn last(mut self) -> Option<char> {
        self.next_back()
    }
}

impl DoubleEndedIterator for Drain<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<char> {
        self.iter.next_back()
    }
}

impl FusedIterator for Drain<'_> {}

#[cfg(test)]
mod tests {
    use crate::String;

    #[test]
    fn drain_front() {
        let mut s = String::<8>::try_from("abcd").unwrap();
        let mut it = s.drain(..1);
        assert_eq!(it.next(), Some('a'));
        drop(it);
        assert_eq!(s, "bcd");
    }

    #[test]
    fn drain_middle() {
        let mut s = String::<8>::try_from("abcd").unwrap();
        let mut it = s.drain(1..3);
        assert_eq!(it.next(), Some('b'));
        assert_eq!(it.next(), Some('c'));
        drop(it);
        assert_eq!(s, "ad");
    }

    #[test]
    fn drain_end() {
        let mut s = String::<8>::try_from("abcd").unwrap();
        let mut it = s.drain(3..);
        assert_eq!(it.next(), Some('d'));
        drop(it);
        assert_eq!(s, "abc");
    }
}

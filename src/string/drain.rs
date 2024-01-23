use core::{fmt, iter::FusedIterator, str::Chars};

use super::String;

/// A draining iterator for `String`.
///
/// This struct is created by the [`drain`] method on [`String`]. See its
/// documentation for more.
///
/// [`drain`]: String::drain
pub struct Drain<'a, const N: usize> {
    /// Will be used as &'a mut String in the destructor
    pub(super) string: *mut String<N>,
    /// Start of part to remove
    pub(super) start: usize,
    /// End of part to remove
    pub(super) end: usize,
    /// Current remaining range to remove
    pub(super) iter: Chars<'a>,
}

impl<const N: usize> fmt::Debug for Drain<'_, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Drain").field(&self.as_str()).finish()
    }
}

unsafe impl<const N: usize> Sync for Drain<'_, N> {}
unsafe impl<const N: usize> Send for Drain<'_, N> {}

impl<const N: usize> Drop for Drain<'_, N> {
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

impl<'a, const N: usize> Drain<'a, N> {
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

impl<const N: usize> AsRef<str> for Drain<'_, N> {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<const N: usize> AsRef<[u8]> for Drain<'_, N> {
    fn as_ref(&self) -> &[u8] {
        self.as_str().as_bytes()
    }
}

impl<const N: usize> Iterator for Drain<'_, N> {
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

impl<const N: usize> DoubleEndedIterator for Drain<'_, N> {
    #[inline]
    fn next_back(&mut self) -> Option<char> {
        self.iter.next_back()
    }
}

impl<const N: usize> FusedIterator for Drain<'_, N> {}

#[cfg(test)]
mod tests {
    use super::String;

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

use core::marker::Unsize;
use core::{fmt, ops, str};
use core::str::Utf8Error;

use {BufferFullError, Vec};
//use core::ops::Deref;

/// A String, backed by a fixed size array `heapless::Vec`
///
/// String: https://doc.rust-lang.org/std/string/struct.String.html

pub struct String<A>
where
    // FIXME(rust-lang/rust#44580) use "const generics" instead of `Unsize`
    A: Unsize<[u8]>,
{
    vec: Vec<u8, A>,
}

impl<A> String<A>
where
    A: Unsize<[u8]>,
{
    /// Constructs a new, empty `String` backed by a `Vec<u8,[u8;N]>`
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    ///
    /// let mut s: String<[u8; 4]> = String::new();
    /// ```
    #[inline]
    pub const fn new() -> Self {
        String { vec: Vec::new() }
    }

    /// Constructs a new, empty `String` backed by a `Vec<u8,[u8;N]>` from an `&str`.
    ///
    /// Cannot be called from a `static` context (not a `const fn`).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    ///
    /// let s: String<[u8; 4]> = String::from("123");
    /// assert!(s.len() == 3);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if capacity of the String would be exceeded.
    ///
    /// ``` should_panic
    /// use heapless::String;
    ///
    /// let s: String<[_; 4]> = String::from("12345"); // <- Would `panic!`
    /// ```
    //
    // Todo, Trait implementation?
    #[inline]
    pub fn from(s: &str) -> Self {
        let mut new = String::new();
        new.push_str(s).unwrap();
        new
    }

    /// Converts a vector of bytes to a `String`.
    ///
    /// A string slice ([`&str`]) is made of bytes ([`u8`]), and a vector of bytes
    /// ([`Vec<u8>`]) is made of bytes, so this function converts between the
    /// two. Not all byte slices are valid `String`s, however: `String`
    /// requires that it is valid UTF-8. `from_utf8()` checks to ensure that
    /// the bytes are valid UTF-8, and then does the conversion.
    ///
    /// See std::String for further information.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::{String, Vec};
    ///
    /// let mut v: Vec<u8, [u8; 8]> = Vec::new();
    /// v.push('a' as u8).unwrap();
    /// v.push('b' as u8).unwrap();
    ///
    /// let s = String::from_utf8(v).unwrap();
    /// assert!(s.len() == 2);
    /// ```
    ///
    /// Incorrect bytes:
    ///
    /// ```
    /// use heapless::{String, Vec};
    ///
    /// // some invalid bytes, in a vector
    ///
    /// let mut v: Vec<u8, [u8; 8]> = Vec::new();
    /// v.push(0).unwrap();
    /// v.push(159).unwrap();
    /// v.push(146).unwrap();
    /// v.push(150).unwrap();
    /// assert!(String::from_utf8(v).is_err());
    /// ```
    #[inline]
    pub fn from_utf8(vec: Vec<u8, A>) -> Result<(String<A>), Utf8Error> {
        {
            let buffer: &[u8] = unsafe { vec.buffer.as_ref() };
            str::from_utf8(&buffer[0..vec.len])?;
        }
        Ok(String { vec: vec })
    }

    /// Converts a vector of bytes to a `String` without checking that the
    /// string contains valid UTF-8.
    ///
    /// See the safe version, [`from_utf8`], for more details.
    #[inline]
    pub unsafe fn from_utf8_unchecked(vec: Vec<u8, A>) -> String<A> {
        String { vec: vec }
    }

    /// Converts a `String` into a byte vector.
    ///
    /// This consumes the `String`, so we do not need to copy its contents.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    ///
    /// let s: String<[_; 4]> = String::from("ab");
    /// let b = s.into_bytes();
    /// assert!(b.len() == 2);
    ///
    /// assert_eq!(&['a' as u8, 'b' as u8], &b[..]);
    /// ```
    #[inline]
    pub fn into_bytes(self) -> Vec<u8, A> {
        self.vec
    }

    /// Extracts a string slice containing the entire string.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    ///
    /// let mut s: String<[_; 4]> = String::from("ab");
    /// assert!(s.as_str() == "ab");
    ///
    /// let _s = s.as_str();
    /// // s.push('c'); // <- cannot borrow `s` as mutable because it is also borrowed as immutable
    /// ```
    #[inline]
    pub fn as_str(&self) -> &str {
        let buffer: &[u8] = unsafe { self.vec.buffer.as_ref() };
        unsafe { str::from_utf8_unchecked(&buffer[..self.vec.len]) }
    }

    /// Converts a `String` into a mutable string slice.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    ///
    /// let mut s: String<[_; 4]> = String::from("ab");
    /// let s = s.as_mut_str();
    /// s.make_ascii_uppercase();
    /// ```
    #[inline]
    pub fn as_mut_str(&mut self) -> &mut str {
        let buffer: &mut [u8] = unsafe { self.vec.buffer.as_mut() };
        unsafe { str::from_utf8_unchecked_mut(&mut buffer[..self.vec.len]) }
    }

    /// Appends a given string slice onto the end of this `String`.
    /// Returns with a Result<(), BufferFullError>.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    ///
    /// let mut s: String<[u8; 8]> = String::from("foo");
    ///
    /// assert!(s.push_str("bar").is_ok());
    ///
    /// assert_eq!("foobar", s);
    ///
    /// assert!(s.push_str("tender").is_err());
    /// ```
    //
    // TODO, should be implemented using `extend_from_slice` on Vec
    // (this is not yet implemented in Vec, so we implement it here)
    #[inline]
    pub fn push_str(&mut self, s: &str) -> Result<(), BufferFullError> {
        let buffer: &mut [u8] = unsafe { self.vec.buffer.as_mut() };
        let start = self.vec.len;
        let new_len = start + s.len();
        if new_len <= buffer.len() {
            self.vec.len = new_len;
            buffer[start..self.vec.len].copy_from_slice(
                &s.as_bytes()[0..self.vec.len.saturating_sub(start)],
            );
            Ok(())
        } else {
            Err(BufferFullError)
        }
    }

    /// Returns the maximum number of elements the String can hold
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    ///
    /// let mut s: String<[u8; 4]> = String::new();
    /// assert!(s.capacity() == 4);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        let buffer: &[u8] = unsafe { self.vec.buffer.as_ref() };
        buffer.len()
    }

    /// Appends the given [`char`] to the end of this `String`.
    /// Assumes ch.len_utf8() == 1
    ///
    /// [`char`]: ../../std/primitive.char.html
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    ///
    /// let mut s: String<[u8; 8]> = String::from("abc");
    ///
    /// s.push('1').unwrap();
    /// s.push('2').unwrap();
    /// s.push('3').unwrap();
    ///
    /// assert!("abc123" == s.as_str());
    ///
    /// assert_eq!("abc123", s);
    /// ```
    #[inline]
    pub fn push(&mut self, c: char) -> Result<(), BufferFullError> {
        self.vec.push(c as u8)
    }

    /// Returns a byte slice of this `String`'s contents.
    ///
    /// The inverse of this method is [`from_utf8`].
    ///
    /// [`from_utf8`]: #method.from_utf8
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    ///
    /// let s: String<[u8; 8]> = String::from("hello");
    ///
    /// assert_eq!(&[104, 101, 108, 108, 111], s.as_bytes());
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        &self.vec
    }

    /// Shortens this `String` to the specified length.
    ///
    /// If `new_len` is greater than the string's current length, this has no
    /// effect.
    ///
    /// Note that this method has no effect on the allocated capacity
    /// of the string
    ///
    /// # Panics
    ///
    /// Panics if `new_len` does not lie on a [`char`] boundary.
    ///
    /// [`char`]: ../../std/primitive.char.html
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    ///
    /// let mut s: String<[u8; 8]> = String::from("hello");
    ///
    /// s.truncate(2);
    ///
    /// assert_eq!("he", s);
    /// ```
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        if new_len <= self.len() {
            assert!(self.is_char_boundary(new_len));
            self.vec.truncate(new_len)
        }
    }

    /// Removes the last character from the string buffer and returns it.
    ///
    /// Returns [`None`] if this `String` is empty.
    ///
    /// [`None`]: ../../std/option/enum.Option.html#variant.None
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    ///
    /// let mut s: String<[u8; 8]> = String::from("foo");
    ///
    /// assert_eq!(s.pop(), Some('o'));
    /// assert_eq!(s.pop(), Some('o'));
    /// assert_eq!(s.pop(), Some('f'));
    ///
    /// assert_eq!(s.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<char> {
        let ch = self.chars().rev().next()?;
        let newlen = self.len() - ch.len_utf8();
        self.vec.len = newlen;

        Some(ch)
    }

    ///
    /// Returns `true` if this `String` has a length of zero.
    ///
    /// Returns `false` otherwise.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    ///
    /// let mut v: String<[u8; 8]> = String::new();
    /// assert!(v.is_empty());
    ///
    /// v.push('a');
    /// assert!(!v.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.vec.len == 0
    }

    /// Truncates this `String`, removing all contents.
    ///
    /// While this means the `String` will have a length of zero, it does not
    /// touch its capacity.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    ///
    /// let mut s: String<[u8; 8]> = String::from("foo");
    ///
    /// s.clear();
    ///
    /// assert!(s.is_empty());
    /// assert_eq!(0, s.len());
    /// assert_eq!(8, s.capacity());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.vec.clear()
    }

    /// Returns the length of this `String`, in bytes.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    ///
    /// let a: String<[u8; 8]> = String::from("foo");
    ///
    /// assert_eq!(a.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.vec.len
    }
}

impl<A> fmt::Debug for String<A>
where
    A: Unsize<[u8]>,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let slice: &str = match str::from_utf8(&*self.vec) {
            Ok(s) => s,
            Err(_) => "could not convert to String",
        };
        slice.fmt(f)
    }
}

impl<A> fmt::Write for String<A>
where
    A: Unsize<[u8]>,
{
    fn write_str(&mut self, s: &str) -> Result<(), fmt::Error> {
        self.push_str(s).unwrap();
        Ok(())
    }

    // fn write_char(&mut self, c: char) -> Result<(), fmt::Error> {
    //     self.push(c);
    //     Ok(())
    // }
}

impl<A> ops::Deref for String<A>
where
    A: Unsize<[u8]>,
{
    type Target = str;

    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl<A> ops::DerefMut for String<A>
where
    A: Unsize<[u8]>,
{
    fn deref_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl<A, B> PartialEq<String<B>> for String<A>
where
    A: Unsize<[u8]>,
    B: Unsize<[u8]>,
{
    fn eq(&self, rhs: &String<B>) -> bool {
        PartialEq::eq(&**self, &**rhs)
    }

    fn ne(&self, rhs: &String<B>) -> bool {
        PartialEq::ne(&**self, &**rhs)
    }
}

macro_rules! impl_eq {
    ($lhs:ty, $rhs: ty) => {

        impl<'a, 'b, A> PartialEq<$rhs> for $lhs
        where
            A: Unsize<[u8]>,
        {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool { PartialEq::eq(&self[..], &other[..]) }
            #[inline]
            fn ne(&self, other: &$rhs) -> bool { PartialEq::ne(&self[..], &other[..]) }
        }

        impl<'a, 'b, A> PartialEq<$lhs> for $rhs
        where
            A: Unsize<[u8]>,
        {
            #[inline]
            fn eq(&self, other: &$lhs) -> bool { PartialEq::eq(&self[..], &other[..]) }
            #[inline]
            fn ne(&self, other: &$lhs) -> bool { PartialEq::ne(&self[..], &other[..]) }
        }

    }
}

impl_eq! { String<A>, str }
impl_eq! { String<A>, &'a str }

impl<A> Eq for String<A>
where
    A: Unsize<[u8]>,
{
}

#[cfg(test)]
mod tests {
    use {String, Vec};

    #[test]
    fn empty() {
        let s: String<[u8; 4]> = String::new();
        assert!(s.capacity() == 4);
        assert_eq!(s, "");
        assert_eq!(s.len(), 0);
        assert_ne!(s.len(), 4);
    }

    #[test]
    fn from() {
        let s: String<[u8; 4]> = String::from("123");
        assert!(s.len() == 3);
        assert_eq!(s, "123");
    }

    #[test]
    #[should_panic]
    fn from_panic() {
        let _: String<[u8; 4]> = String::from("12345");
    }

    #[test]
    fn from_utf8() {
        let mut v: Vec<u8, [u8; 8]> = Vec::new();
        v.push('a' as u8).unwrap();
        v.push('b' as u8).unwrap();

        let s = String::from_utf8(v).unwrap();
        assert_eq!(s, "ab");
    }

    #[test]
    fn from_utf8_uenc() {
        let mut v: Vec<u8, [u8; 8]> = Vec::new();
        v.push(240).unwrap();
        v.push(159).unwrap();
        v.push(146).unwrap();
        v.push(150).unwrap();

        assert!(String::from_utf8(v).is_ok());
    }

    #[test]
    fn from_utf8_uenc_err() {
        let mut v: Vec<u8, [u8; 8]> = Vec::new();
        v.push(0).unwrap();
        v.push(159).unwrap();
        v.push(146).unwrap();
        v.push(150).unwrap();

        assert!(String::from_utf8(v).is_err());
    }

    #[test]
    fn from_utf8_unchecked() {
        let mut v: Vec<u8, [u8; 8]> = Vec::new();
        v.push(0).unwrap();
        v.push(159).unwrap();
        v.push(146).unwrap();
        v.push(150).unwrap();

        let s = unsafe { String::from_utf8_unchecked(v) };
    }

    #[test]
    fn into_bytes() {
        let s: String<[_; 4]> = String::from("ab");
        let b: Vec<u8, [u8; 4]> = s.into_bytes();
        assert_eq!(b.len(), 2);
        assert_eq!(&['a' as u8, 'b' as u8], &b[..]);
    }

    #[test]
    fn as_str() {
        let s: String<[_; 4]> = String::from("ab");

        assert_eq!(s.as_str(), "ab");
        // should be moved to fail test
        //    let _s = s.as_str();
        // s.push('c'); // <- cannot borrow `s` as mutable because it is also borrowed as immutable
    }

    #[test]
    fn as_mut_str() {
        let mut s: String<[_; 4]> = String::from("ab");
        let s = s.as_mut_str();
        s.make_ascii_uppercase();
        assert_eq!(s, "AB");
    }

    #[test]
    fn push_str() {
        let mut s: String<[u8; 8]> = String::from("foo");
        assert!(s.push_str("bar").is_ok());
        assert_eq!("foobar", s);
        assert!(s.push_str("tender").is_err());
        assert_eq!("foobar", s);
    }

    #[test]
    fn push() {
        let mut s: String<[u8; 6]> = String::from("abc");
        s.push('1').is_ok();
        s.push('2').is_ok();
        s.push('3').is_ok();
        s.push('4').is_err();
        assert!("abc123" == s.as_str());
    }

    #[test]
    fn as_bytes() {
        let s: String<[u8; 8]> = String::from("hello");
        assert_eq!(&[104, 101, 108, 108, 111], s.as_bytes());
    }

    #[test]
    fn truncate() {
        let mut s: String<[u8; 8]> = String::from("hello");
        s.truncate(6);
        assert_eq!(s.len(), 5);
        s.truncate(2);
        assert_eq!(s.len(), 2);
        assert_eq!("he", s);
        assert_eq!(s, "he");
    }

    #[test]
    fn pop() {
        let mut s: String<[u8; 8]> = String::from("foo");
        assert_eq!(s.pop(), Some('o'));
        assert_eq!(s.pop(), Some('o'));
        assert_eq!(s.pop(), Some('f'));
        assert_eq!(s.pop(), None);
    }

    #[test]
    fn pop_uenc() {
        let mut s: String<[u8; 8]> = String::from("é");
        assert_eq!(s.len(), 3);
        match s.pop() {
            Some(c) => {
                assert_eq!(s.len(), 1);
                assert_eq!(c, '\u{0301}'); // accute accent of e
                ()
            }
            None => assert!(false),
        };
    }

    #[test]
    fn is_empty() {
        let mut v: String<[u8; 8]> = String::new();
        assert!(v.is_empty());
        let _ = v.push('a');
        assert!(!v.is_empty());
    }

    #[test]
    fn clear() {
        let mut s: String<[u8; 8]> = String::from("foo");
        s.clear();
        assert!(s.is_empty());
        assert_eq!(0, s.len());
        assert_eq!(8, s.capacity());
    }

}

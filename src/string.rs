use core::{fmt, fmt::Write, hash, mem, ops, str, str::Utf8Error};

use generic_array::{
    typenum::{consts::*, IsGreaterOrEqual},
    ArrayLength, GenericArray,
};
use hash32;

use crate::Vec;

/// A fixed capacity [`String`](https://doc.rust-lang.org/std/string/struct.String.html)
pub struct String<N>(#[doc(hidden)] pub crate::i::String<GenericArray<u8, N>>)
where
    N: ArrayLength<u8>;

impl<A> crate::i::String<A> {
    /// `String` `const` constructor; wrap the returned value in [`String`](../struct.String.html)
    pub const fn new() -> Self {
        Self {
            vec: crate::i::Vec::new(),
        }
    }
}

impl<N> String<N>
where
    N: ArrayLength<u8>,
{
    /// Constructs a new, empty `String` with a fixed capacity of `N`
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    /// use heapless::consts::*;
    ///
    /// // allocate the string on the stack
    /// let mut s: String<U4> = String::new();
    ///
    /// // allocate the string in a static variable
    /// static mut S: String<U4> = String(heapless::i::String::new());
    /// ```
    #[inline]
    pub fn new() -> Self {
        String(crate::i::String::new())
    }

    /// Converts a vector of bytes into a `String`.
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
    /// use heapless::consts::*;
    ///
    /// let mut v: Vec<u8, U8> = Vec::new();
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
    /// use heapless::consts::*;
    ///
    /// // some invalid bytes, in a vector
    ///
    /// let mut v: Vec<u8, U8> = Vec::new();
    /// v.push(0).unwrap();
    /// v.push(159).unwrap();
    /// v.push(146).unwrap();
    /// v.push(150).unwrap();
    /// assert!(String::from_utf8(v).is_err());
    /// ```
    #[inline]
    pub fn from_utf8(vec: Vec<u8, N>) -> Result<(String<N>), Utf8Error> {
        // validate input
        str::from_utf8(&*vec)?;

        Ok(unsafe { String::from_utf8_unchecked(vec) })
    }

    /// Converts a vector of bytes to a `String` without checking that the
    /// string contains valid UTF-8.
    ///
    /// See the safe version, `from_utf8`, for more details.
    #[inline]
    pub unsafe fn from_utf8_unchecked(mut vec: Vec<u8, N>) -> String<N> {
        // FIXME this may result in a memcpy at runtime
        let vec_ = mem::replace(&mut vec.0, mem::uninitialized());
        mem::forget(vec);
        String(crate::i::String { vec: vec_ })
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
    /// use heapless::consts::*;
    ///
    /// let s: String<U4> = String::from("ab");
    /// let b = s.into_bytes();
    /// assert!(b.len() == 2);
    ///
    /// assert_eq!(&['a' as u8, 'b' as u8], &b[..]);
    /// ```
    #[inline]
    pub fn into_bytes(self) -> Vec<u8, N> {
        Vec(self.0.vec)
    }

    /// Extracts a string slice containing the entire string.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    /// use heapless::consts::*;
    ///
    /// let mut s: String<U4> = String::from("ab");
    /// assert!(s.as_str() == "ab");
    ///
    /// let _s = s.as_str();
    /// // s.push('c'); // <- cannot borrow `s` as mutable because it is also borrowed as immutable
    /// ```
    #[inline]
    pub fn as_str(&self) -> &str {
        unsafe { str::from_utf8_unchecked(self.0.vec.as_slice()) }
    }

    /// Converts a `String` into a mutable string slice.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    /// use heapless::consts::*;
    ///
    /// let mut s: String<U4> = String::from("ab");
    /// let s = s.as_mut_str();
    /// s.make_ascii_uppercase();
    /// ```
    #[inline]
    pub fn as_mut_str(&mut self) -> &mut str {
        unsafe { str::from_utf8_unchecked_mut(self.0.vec.as_mut_slice()) }
    }

    /// Appends a given string slice onto the end of this `String`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    /// use heapless::consts::*;
    ///
    /// let mut s: String<U8> = String::from("foo");
    ///
    /// assert!(s.push_str("bar").is_ok());
    ///
    /// assert_eq!("foobar", s);
    ///
    /// assert!(s.push_str("tender").is_err());
    /// ```
    #[inline]
    pub fn push_str(&mut self, string: &str) -> Result<(), ()> {
        self.0.vec.extend_from_slice(string.as_bytes())
    }

    /// Returns the maximum number of elements the String can hold
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    /// use heapless::consts::*;
    ///
    /// let mut s: String<U4> = String::new();
    /// assert!(s.capacity() == 4);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        self.0.vec.capacity()
    }

    /// Appends the given [`char`] to the end of this `String`.
    ///
    /// [`char`]: ../../std/primitive.char.html
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    /// use heapless::consts::*;
    ///
    /// let mut s: String<U8> = String::from("abc");
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
    pub fn push(&mut self, c: char) -> Result<(), ()> {
        match c.len_utf8() {
            1 => self.0.vec.push(c as u8).map_err(|_| {}),
            _ => self
                .0
                .vec
                .extend_from_slice(c.encode_utf8(&mut [0; 4]).as_bytes()),
        }
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
    /// use heapless::consts::*;
    ///
    /// let mut s: String<U8> = String::from("hello");
    ///
    /// s.truncate(2);
    ///
    /// assert_eq!("he", s);
    /// ```
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        if new_len <= self.len() {
            assert!(self.is_char_boundary(new_len));
            self.0.vec.truncate(new_len)
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
    /// use heapless::consts::*;
    ///
    /// let mut s: String<U8> = String::from("foo");
    ///
    /// assert_eq!(s.pop(), Some('o'));
    /// assert_eq!(s.pop(), Some('o'));
    /// assert_eq!(s.pop(), Some('f'));
    ///
    /// assert_eq!(s.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<char> {
        let ch = self.chars().rev().next()?;

        // pop bytes that correspond to `ch`
        for _ in 0..ch.len_utf8() {
            unsafe {
                self.0.vec.pop_unchecked();
            }
        }

        Some(ch)
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
    /// use heapless::consts::*;
    ///
    /// let mut s: String<U8> = String::from("foo");
    ///
    /// s.clear();
    ///
    /// assert!(s.is_empty());
    /// assert_eq!(0, s.len());
    /// assert_eq!(8, s.capacity());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.0.vec.clear()
    }
}

impl<N> Default for String<N>
where
    N: ArrayLength<u8>,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, N> From<&'a str> for String<N>
where
    N: ArrayLength<u8>,
{
    fn from(s: &'a str) -> Self {
        let mut new = String::new();
        new.push_str(s).unwrap();
        new
    }
}

impl<N> str::FromStr for String<N>
where
    N: ArrayLength<u8>,
{
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut new = String::new();
        new.push_str(s)?;
        Ok(new)
    }
}

impl<N> Clone for String<N>
where
    N: ArrayLength<u8>,
{
    fn clone(&self) -> Self {
        Self(crate::i::String {
            vec: self.0.vec.clone(),
        })
    }
}

impl<N> fmt::Debug for String<N>
where
    N: ArrayLength<u8>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <str as fmt::Debug>::fmt(self, f)
    }
}

impl<N> fmt::Display for String<N>
where
    N: ArrayLength<u8>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <str as fmt::Display>::fmt(self, f)
    }
}

impl<N> hash::Hash for String<N>
where
    N: ArrayLength<u8>,
{
    #[inline]
    fn hash<H: hash::Hasher>(&self, hasher: &mut H) {
        <str as hash::Hash>::hash(self, hasher)
    }
}

impl<N> hash32::Hash for String<N>
where
    N: ArrayLength<u8>,
{
    #[inline]
    fn hash<H: hash32::Hasher>(&self, hasher: &mut H) {
        <str as hash32::Hash>::hash(self, hasher)
    }
}

impl<N> fmt::Write for String<N>
where
    N: ArrayLength<u8>,
{
    fn write_str(&mut self, s: &str) -> Result<(), fmt::Error> {
        self.push_str(s).map_err(|_| fmt::Error)
    }

    fn write_char(&mut self, c: char) -> Result<(), fmt::Error> {
        self.push(c).map_err(|_| fmt::Error)
    }
}

impl<N> ops::Deref for String<N>
where
    N: ArrayLength<u8>,
{
    type Target = str;

    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl<N> ops::DerefMut for String<N>
where
    N: ArrayLength<u8>,
{
    fn deref_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl<N> AsRef<str> for String<N>
where
    N: ArrayLength<u8>,
{
    #[inline]
    fn as_ref(&self) -> &str {
        self
    }
}

impl<N> AsRef<[u8]> for String<N>
where
    N: ArrayLength<u8>,
{
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<N1, N2> PartialEq<String<N2>> for String<N1>
where
    N1: ArrayLength<u8>,
    N2: ArrayLength<u8>,
{
    fn eq(&self, rhs: &String<N2>) -> bool {
        str::eq(&**self, &**rhs)
    }

    fn ne(&self, rhs: &String<N2>) -> bool {
        str::ne(&**self, &**rhs)
    }
}

macro_rules! impl_eq {
    ($lhs:ty, $rhs:ty) => {
        impl<'a, 'b, N> PartialEq<$rhs> for $lhs
        where
            N: ArrayLength<u8>,
        {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool {
                str::eq(&self[..], &other[..])
            }
            #[inline]
            fn ne(&self, other: &$rhs) -> bool {
                str::ne(&self[..], &other[..])
            }
        }

        impl<'a, 'b, N> PartialEq<$lhs> for $rhs
        where
            N: ArrayLength<u8>,
        {
            #[inline]
            fn eq(&self, other: &$lhs) -> bool {
                str::eq(&self[..], &other[..])
            }
            #[inline]
            fn ne(&self, other: &$lhs) -> bool {
                str::ne(&self[..], &other[..])
            }
        }
    };
}

impl_eq! { String<N>, str }
impl_eq! { String<N>, &'a str }

impl<N> Eq for String<N> where N: ArrayLength<u8> {}

macro_rules! impl_from_num {
    ($num:ty, $size:ty) => {
        impl<N> From<$num> for String<N>
        where
            N: ArrayLength<u8> + IsGreaterOrEqual<$size, Output = True>,
        {
            fn from(s: $num) -> Self {
                let mut new = String::new();
                write!(&mut new, "{}", s).unwrap();
                new
            }
        }
    };
}

impl_from_num!(i8, U4);
impl_from_num!(i16, U6);
impl_from_num!(i32, U11);
impl_from_num!(i64, U20);

impl_from_num!(u8, U3);
impl_from_num!(u16, U5);
impl_from_num!(u32, U10);
impl_from_num!(u64, U20);

#[cfg(test)]
mod tests {
    use crate::{consts::*, String, Vec};

    #[test]
    fn static_new() {
        static mut _S: String<U8> = String(crate::i::String::new());
    }

    #[test]
    fn clone() {
        let s1: String<U20> = String::from("abcd");
        let mut s2 = s1.clone();
        s2.push_str(" efgh").unwrap();

        assert_eq!(s1, "abcd");
        assert_eq!(s2, "abcd efgh");
    }

    #[test]
    fn debug() {
        use core::fmt::Write;

        let s: String<U8> = String::from("abcd");
        let mut std_s = std::string::String::new();
        write!(std_s, "{:?}", s).unwrap();
        assert_eq!("\"abcd\"", std_s);
    }

    #[test]
    fn display() {
        use core::fmt::Write;

        let s: String<U8> = String::from("abcd");
        let mut std_s = std::string::String::new();
        write!(std_s, "{}", s).unwrap();
        assert_eq!("abcd", std_s);
    }

    #[test]
    fn empty() {
        let s: String<U4> = String::new();
        assert!(s.capacity() == 4);
        assert_eq!(s, "");
        assert_eq!(s.len(), 0);
        assert_ne!(s.len(), 4);
    }

    #[test]
    fn from() {
        let s: String<U4> = String::from("123");
        assert!(s.len() == 3);
        assert_eq!(s, "123");
    }

    #[test]
    fn from_str() {
        use core::str::FromStr;

        let s: String<U4> = String::<U4>::from_str("123").unwrap();
        assert!(s.len() == 3);
        assert_eq!(s, "123");

        let e: () = String::<U2>::from_str("123").unwrap_err();
        assert_eq!(e, ());
    }

    #[test]
    #[should_panic]
    fn from_panic() {
        let _: String<U4> = String::from("12345");
    }

    #[test]
    fn from_utf8() {
        let mut v: Vec<u8, U8> = Vec::new();
        v.push('a' as u8).unwrap();
        v.push('b' as u8).unwrap();

        let s = String::from_utf8(v).unwrap();
        assert_eq!(s, "ab");
    }

    #[test]
    fn from_utf8_uenc() {
        let mut v: Vec<u8, U8> = Vec::new();
        v.push(240).unwrap();
        v.push(159).unwrap();
        v.push(146).unwrap();
        v.push(150).unwrap();

        assert!(String::from_utf8(v).is_ok());
    }

    #[test]
    fn from_utf8_uenc_err() {
        let mut v: Vec<u8, U8> = Vec::new();
        v.push(0).unwrap();
        v.push(159).unwrap();
        v.push(146).unwrap();
        v.push(150).unwrap();

        assert!(String::from_utf8(v).is_err());
    }

    #[test]
    fn from_utf8_unchecked() {
        let mut v: Vec<u8, U8> = Vec::new();
        v.push(104).unwrap();
        v.push(101).unwrap();
        v.push(108).unwrap();
        v.push(108).unwrap();
        v.push(111).unwrap();

        let s = unsafe { String::from_utf8_unchecked(v) };

        assert_eq!(s, "hello");
    }

    #[test]
    fn from_num() {
        let v = String::<U20>::from(18446744073709551615 as u64);

        assert_eq!(v, "18446744073709551615");
    }

    #[test]
    fn into_bytes() {
        let s: String<U4> = String::from("ab");
        let b: Vec<u8, U4> = s.into_bytes();
        assert_eq!(b.len(), 2);
        assert_eq!(&['a' as u8, 'b' as u8], &b[..]);
    }

    #[test]
    fn as_str() {
        let s: String<U4> = String::from("ab");

        assert_eq!(s.as_str(), "ab");
        // should be moved to fail test
        //    let _s = s.as_str();
        // s.push('c'); // <- cannot borrow `s` as mutable because it is also borrowed as immutable
    }

    #[test]
    fn as_mut_str() {
        let mut s: String<U4> = String::from("ab");
        let s = s.as_mut_str();
        s.make_ascii_uppercase();
        assert_eq!(s, "AB");
    }

    #[test]
    fn push_str() {
        let mut s: String<U8> = String::from("foo");
        assert!(s.push_str("bar").is_ok());
        assert_eq!("foobar", s);
        assert!(s.push_str("tender").is_err());
        assert_eq!("foobar", s);
    }

    #[test]
    fn push() {
        let mut s: String<U6> = String::from("abc");
        assert!(s.push('1').is_ok());
        assert!(s.push('2').is_ok());
        assert!(s.push('3').is_ok());
        assert!(s.push('4').is_err());
        assert!("abc123" == s.as_str());
    }

    #[test]
    fn as_bytes() {
        let s: String<U8> = String::from("hello");
        assert_eq!(&[104, 101, 108, 108, 111], s.as_bytes());
    }

    #[test]
    fn truncate() {
        let mut s: String<U8> = String::from("hello");
        s.truncate(6);
        assert_eq!(s.len(), 5);
        s.truncate(2);
        assert_eq!(s.len(), 2);
        assert_eq!("he", s);
        assert_eq!(s, "he");
    }

    #[test]
    fn pop() {
        let mut s: String<U8> = String::from("foo");
        assert_eq!(s.pop(), Some('o'));
        assert_eq!(s.pop(), Some('o'));
        assert_eq!(s.pop(), Some('f'));
        assert_eq!(s.pop(), None);
    }

    #[test]
    fn pop_uenc() {
        let mut s: String<U8> = String::from("é");
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
        let mut v: String<U8> = String::new();
        assert!(v.is_empty());
        let _ = v.push('a');
        assert!(!v.is_empty());
    }

    #[test]
    fn clear() {
        let mut s: String<U8> = String::from("foo");
        s.clear();
        assert!(s.is_empty());
        assert_eq!(0, s.len());
        assert_eq!(8, s.capacity());
    }

}

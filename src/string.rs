use core::{fmt, fmt::Write, hash, ops, str};

use hash32;

use crate::{sealed::spsc::Uxx, Vec};

/// A fixed capacity [`String`](https://doc.rust-lang.org/std/string/struct.String.html)
pub struct String<U: Uxx, const N: usize> {
    vec: Vec<u8, U, N>,
}

macro_rules! impl_new {
    ($Uxx:ident, $name:ident) => {
        impl<const N: usize> String<$Uxx, N> {
            /// Constructs a new, empty `String` with a fixed capacity of `N`
            #[inline]
            pub const fn $name() -> Self {
                Self { vec: Vec::$name() }
            }
        }
    };
}

impl_new!(u8, u8);
impl_new!(u16, u16);
impl_new!(usize, usize);

impl<const N: usize> String<usize, N> {
    /// Constructs a new, empty `String` with a fixed capacity of `N` and length type of `usize`
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    ///
    /// // allocate the string on the stack
    /// let mut s: String<_, 4> = String::new();
    ///
    /// // allocate the string in a static variable
    /// static mut S: String<usize, 4> = String::new();
    /// ```
    #[inline]
    pub const fn new() -> Self {
        Self { vec: Vec::new() }
    }
}

impl<U: Uxx, const N: usize> String<U, N> {
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
    /// let s: String<4> = String::from("ab");
    /// let b = s.into_bytes();
    /// assert!(b.len() == 2);
    ///
    /// assert_eq!(&['a' as u8, 'b' as u8], &b[..]);
    /// ```
    #[inline]
    pub fn into_bytes(self) -> Vec<u8, U, N> {
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
    /// let mut s: String<4> = String::from("ab");
    /// assert!(s.as_str() == "ab");
    ///
    /// let _s = s.as_str();
    /// // s.push('c'); // <- cannot borrow `s` as mutable because it is also borrowed as immutable
    /// ```
    #[inline]
    pub fn as_str(&self) -> &str {
        unsafe { str::from_utf8_unchecked(self.vec.as_slice()) }
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
    /// let mut s: String<4> = String::from("ab");
    /// let s = s.as_mut_str();
    /// s.make_ascii_uppercase();
    /// ```
    #[inline]
    pub fn as_mut_str(&mut self) -> &mut str {
        unsafe { str::from_utf8_unchecked_mut(self.vec.as_mut_slice()) }
    }

    /// Returns a mutable reference to the contents of this `String`.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not check that the bytes passed
    /// to it are valid UTF-8. If this constraint is violated, it may cause
    /// memory unsafety issues with future users of the `String`, as the rest of
    /// the library assumes that `String`s are valid UTF-8.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// let mut s = String::from("hello");
    ///
    /// unsafe {
    ///     let vec = s.as_mut_vec();
    ///     assert_eq!(&[104, 101, 108, 108, 111][..], &vec[..]);
    ///
    ///     vec.reverse();
    /// }
    /// assert_eq!(s, "olleh");
    /// ```
    pub unsafe fn as_mut_vec(&mut self) -> &mut Vec<u8, U, N> {
        &mut self.vec
    }

    /// Appends a given string slice onto the end of this `String`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    ///
    /// let mut s: String<8> = String::from("foo");
    ///
    /// assert!(s.push_str("bar").is_ok());
    ///
    /// assert_eq!("foobar", s);
    ///
    /// assert!(s.push_str("tender").is_err());
    /// ```
    #[inline]
    pub fn push_str(&mut self, string: &str) -> Result<(), ()> {
        self.vec.extend_from_slice(string.as_bytes())
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
    /// let mut s: String<4> = String::new();
    /// assert!(s.capacity() == 4);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        self.vec.capacity_nonconst()
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
    ///
    /// let mut s: String<8> = String::from("abc");
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
            1 => self.vec.push(c as u8).map_err(|_| {}),
            _ => self
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
    ///
    /// let mut s: String<8> = String::from("hello");
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
    /// let mut s: String<8> = String::from("foo");
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
                self.vec.pop_unchecked();
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
    ///
    /// let mut s: String<8> = String::from("foo");
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
}

impl<U: Uxx, const N: usize> Default for String<U, N> {
    fn default() -> Self {
        Self {
            vec: Vec::default(),
        }
    }
}

impl<'a, U: Uxx, const N: usize> From<&'a str> for String<U, N> {
    fn from(s: &'a str) -> Self {
        let mut new = String::default();
        new.push_str(s).unwrap();
        new
    }
}

impl<U: Uxx, const N: usize> str::FromStr for String<U, N> {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut new = String::default();
        new.push_str(s)?;
        Ok(new)
    }
}

impl<U: Uxx, const N: usize> Clone for String<U, N> {
    fn clone(&self) -> Self {
        Self {
            vec: self.vec.clone(),
        }
    }
}

impl<U: Uxx, const N: usize> fmt::Debug for String<U, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <str as fmt::Debug>::fmt(self, f)
    }
}

impl<U: Uxx, const N: usize> fmt::Display for String<U, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <str as fmt::Display>::fmt(self, f)
    }
}

impl<U: Uxx, const N: usize> hash::Hash for String<U, N> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, hasher: &mut H) {
        <str as hash::Hash>::hash(self, hasher)
    }
}

impl<U: Uxx, const N: usize> hash32::Hash for String<U, N> {
    #[inline]
    fn hash<H: hash32::Hasher>(&self, hasher: &mut H) {
        <str as hash32::Hash>::hash(self, hasher)
    }
}

impl<U: Uxx, const N: usize> fmt::Write for String<U, N> {
    fn write_str(&mut self, s: &str) -> Result<(), fmt::Error> {
        self.push_str(s).map_err(|_| fmt::Error)
    }

    fn write_char(&mut self, c: char) -> Result<(), fmt::Error> {
        self.push(c).map_err(|_| fmt::Error)
    }
}

impl<U: Uxx, const N: usize> ops::Deref for String<U, N> {
    type Target = str;

    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl<U: Uxx, const N: usize> ops::DerefMut for String<U, N> {
    fn deref_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl<U: Uxx, const N: usize> AsRef<str> for String<U, N> {
    #[inline]
    fn as_ref(&self) -> &str {
        self
    }
}

impl<U: Uxx, const N: usize> AsRef<[u8]> for String<U, N> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<U1: Uxx, U2: Uxx, const N1: usize, const N2: usize> PartialEq<String<U2, N2>>
    for String<U1, N1>
{
    fn eq(&self, rhs: &String<U2, N2>) -> bool {
        str::eq(&**self, &**rhs)
    }

    fn ne(&self, rhs: &String<U2, N2>) -> bool {
        str::ne(&**self, &**rhs)
    }
}

// macro_rules! impl_eq {
//     ($lhs:ty, $rhs:ty) => {
//         impl<'a, 'b, U, N> PartialEq<$rhs> for $lhs
//         where
//             N: ArrayLength<u8>,
//         {
//             #[inline]
//             fn eq(&self, other: &$rhs) -> bool {
//                 str::eq(&self[..], &other[..])
//             }
//             #[inline]
//             fn ne(&self, other: &$rhs) -> bool {
//                 str::ne(&self[..], &other[..])
//             }
//         }

//         impl<'a, 'b, U, N> PartialEq<$lhs> for $rhs
//         where
//             N: ArrayLength<u8>,
//         {
//             #[inline]
//             fn eq(&self, other: &$lhs) -> bool {
//                 str::eq(&self[..], &other[..])
//             }
//             #[inline]
//             fn ne(&self, other: &$lhs) -> bool {
//                 str::ne(&self[..], &other[..])
//             }
//         }
//     };
// }

// String<U, N> == str
impl<U: Uxx, const N: usize> PartialEq<str> for String<U, N> {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        str::eq(&self[..], &other[..])
    }
    #[inline]
    fn ne(&self, other: &str) -> bool {
        str::ne(&self[..], &other[..])
    }
}

// String<U, N> == &'str
impl<U: Uxx, const N: usize> PartialEq<&str> for String<U, N> {
    #[inline]
    fn eq(&self, other: &&str) -> bool {
        str::eq(&self[..], &other[..])
    }
    #[inline]
    fn ne(&self, other: &&str) -> bool {
        str::ne(&self[..], &other[..])
    }
}

// str == String<U, N>
impl<U: Uxx, const N: usize> PartialEq<String<U, N>> for str {
    #[inline]
    fn eq(&self, other: &String<U, N>) -> bool {
        str::eq(&self[..], &other[..])
    }
    #[inline]
    fn ne(&self, other: &String<U, N>) -> bool {
        str::ne(&self[..], &other[..])
    }
}

// &'str == String<U, N>
impl<U: Uxx, const N: usize> PartialEq<String<U, N>> for &str {
    #[inline]
    fn eq(&self, other: &String<U, N>) -> bool {
        str::eq(&self[..], &other[..])
    }
    #[inline]
    fn ne(&self, other: &String<U, N>) -> bool {
        str::ne(&self[..], &other[..])
    }
}

impl<U: Uxx, const N: usize> Eq for String<U, N> {}

macro_rules! impl_from_num {
    ($num:ty, $size:expr) => {
        impl<U: Uxx, const N: usize> From<$num> for String<U, N> {
            fn from(s: $num) -> Self {
                let mut new = String::default();
                write!(&mut new, "{}", s).unwrap();
                new
            }
        }
    };
}

impl_from_num!(i8, 4);
impl_from_num!(i16, 6);
impl_from_num!(i32, 11);
impl_from_num!(i64, 20);

impl_from_num!(u8, 3);
impl_from_num!(u16, 5);
impl_from_num!(u32, 10);
impl_from_num!(u64, 20);

#[cfg(test)]
mod tests {
    use crate::{String, Vec};

    #[test]
    fn static_new() {
        static mut _S: String<8> = String::new();
    }

    #[test]
    fn clone() {
        let s1: String<20> = String::from("abcd");
        let mut s2 = s1.clone();
        s2.push_str(" efgh").unwrap();

        assert_eq!(s1, "abcd");
        assert_eq!(s2, "abcd efgh");
    }

    #[test]
    fn debug() {
        use core::fmt::Write;

        let s: String<8> = String::from("abcd");
        let mut std_s = std::string::String::new();
        write!(std_s, "{:?}", s).unwrap();
        assert_eq!("\"abcd\"", std_s);
    }

    #[test]
    fn display() {
        use core::fmt::Write;

        let s: String<8> = String::from("abcd");
        let mut std_s = std::string::String::new();
        write!(std_s, "{}", s).unwrap();
        assert_eq!("abcd", std_s);
    }

    #[test]
    fn empty() {
        let s: String<4> = String::new();
        assert!(s.capacity() == 4);
        assert_eq!(s, "");
        assert_eq!(s.len(), 0);
        assert_ne!(s.len(), 4);
    }

    #[test]
    fn from() {
        let s: String<4> = String::from("123");
        assert!(s.len() == 3);
        assert_eq!(s, "123");
    }

    #[test]
    fn from_str() {
        use core::str::FromStr;

        let s: String<4> = String::<4>::from_str("123").unwrap();
        assert!(s.len() == 3);
        assert_eq!(s, "123");

        let e: () = String::<2>::from_str("123").unwrap_err();
        assert_eq!(e, ());
    }

    #[test]
    #[should_panic]
    fn from_panic() {
        let _: String<4> = String::from("12345");
    }

    #[test]
    fn from_num() {
        let v: String<20> = String::from(18446744073709551615 as u64);
        assert_eq!(v, "18446744073709551615");
    }

    #[test]
    fn into_bytes() {
        let s: String<4> = String::from("ab");
        let b: Vec<u8, 4> = s.into_bytes();
        assert_eq!(b.len(), 2);
        assert_eq!(&['a' as u8, 'b' as u8], &b[..]);
    }

    #[test]
    fn as_str() {
        let s: String<4> = String::from("ab");

        assert_eq!(s.as_str(), "ab");
        // should be moved to fail test
        //    let _s = s.as_str();
        // s.push('c'); // <- cannot borrow `s` as mutable because it is also borrowed as immutable
    }

    #[test]
    fn as_mut_str() {
        let mut s: String<4> = String::from("ab");
        let s = s.as_mut_str();
        s.make_ascii_uppercase();
        assert_eq!(s, "AB");
    }

    #[test]
    fn push_str() {
        let mut s: String<8> = String::from("foo");
        assert!(s.push_str("bar").is_ok());
        assert_eq!("foobar", s);
        assert_eq!(s, "foobar");
        assert!(s.push_str("tender").is_err());
        assert_eq!("foobar", s);
        assert_eq!(s, "foobar");
    }

    #[test]
    fn push() {
        let mut s: String<6> = String::from("abc");
        assert!(s.push('1').is_ok());
        assert!(s.push('2').is_ok());
        assert!(s.push('3').is_ok());
        assert!(s.push('4').is_err());
        assert!("abc123" == s.as_str());
    }

    #[test]
    fn as_bytes() {
        let s: String<8> = String::from("hello");
        assert_eq!(&[104, 101, 108, 108, 111], s.as_bytes());
    }

    #[test]
    fn truncate() {
        let mut s: String<8> = String::from("hello");
        s.truncate(6);
        assert_eq!(s.len(), 5);
        s.truncate(2);
        assert_eq!(s.len(), 2);
        assert_eq!("he", s);
        assert_eq!(s, "he");
    }

    #[test]
    fn pop() {
        let mut s: String<8> = String::from("foo");
        assert_eq!(s.pop(), Some('o'));
        assert_eq!(s.pop(), Some('o'));
        assert_eq!(s.pop(), Some('f'));
        assert_eq!(s.pop(), None);
    }

    #[test]
    fn pop_uenc() {
        let mut s: String<8> = String::from("é");
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
        let mut v: String<8> = String::new();
        assert!(v.is_empty());
        let _ = v.push('a');
        assert!(!v.is_empty());
    }

    #[test]
    fn clear() {
        let mut s: String<8> = String::from("foo");
        s.clear();
        assert!(s.is_empty());
        assert_eq!(0, s.len());
        assert_eq!(8, s.capacity());
    }
}

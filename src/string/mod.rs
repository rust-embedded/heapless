//! A fixed capacity [`String`](https://doc.rust-lang.org/std/string/struct.String.html).

use core::{
    borrow,
    char::DecodeUtf16Error,
    cmp::Ordering,
    fmt,
    fmt::{Arguments, Write},
    hash, iter,
    ops::{self, Range, RangeBounds},
    str::{self, Utf8Error},
};

use crate::{
    storage::{OwnedStorage, Storage, ViewStorage},
    vec::VecInner,
    Vec,
};

mod drain;
pub use drain::Drain;

/// A possible error value when converting a [`String`] from a UTF-16 byte slice.
///
/// This type is the error type for the [`from_utf16`] method on [`String`].
///
/// [`from_utf16`]: String::from_utf16
#[derive(Debug)]
pub enum FromUtf16Error {
    /// The capacity of the `String` is too small for the given operation.
    Capacity,
    /// Error decoding UTF-16.
    DecodeUtf16Error(DecodeUtf16Error),
}

impl fmt::Display for FromUtf16Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Capacity => "insufficient capacity".fmt(f),
            Self::DecodeUtf16Error(e) => write!(f, "invalid UTF-16: {}", e),
        }
    }
}

/// Base struct for [`String`] and [`StringView`], generic over the [`Storage`].
///
/// In most cases you should use [`String`] or [`StringView`] directly. Only use this
/// struct if you want to write code that's generic over both.
pub struct StringInner<S: Storage> {
    vec: VecInner<u8, S>,
}

/// A fixed capacity [`String`](https://doc.rust-lang.org/std/string/struct.String.html).
pub type String<const N: usize> = StringInner<OwnedStorage<N>>;

/// A dynamic capacity [`String`](https://doc.rust-lang.org/std/string/struct.String.html).
pub type StringView = StringInner<ViewStorage>;

impl StringView {
    /// Removes the specified range from the string in bulk, returning all
    /// removed characters as an iterator.
    ///
    /// The returned iterator keeps a mutable borrow on the string to optimize
    /// its implementation.
    ///
    /// # Panics
    ///
    /// Panics if the starting point or end point do not lie on a [`char`]
    /// boundary, or if they're out of bounds.
    ///
    /// # Leaking
    ///
    /// If the returned iterator goes out of scope without being dropped (due to
    /// [`core::mem::forget`], for example), the string may still contain a copy
    /// of any drained characters, or may have lost characters arbitrarily,
    /// including characters outside the range.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::String;
    ///
    /// let mut s = String::<32>::try_from("α is alpha, β is beta").unwrap();
    /// let beta_offset = s.find('β').unwrap_or(s.len());
    ///
    /// // Remove the range up until the β from the string
    /// let t: String<32> = s.drain(..beta_offset).collect();
    /// assert_eq!(t, "α is alpha, ");
    /// assert_eq!(s, "β is beta");
    ///
    /// // A full range clears the string, like `clear()` does
    /// s.drain(..);
    /// assert_eq!(s, "");
    /// ```
    pub fn drain<R>(&mut self, range: R) -> Drain<'_>
    where
        R: RangeBounds<usize>,
    {
        // Memory safety
        //
        // The `String` version of `Drain` does not have the memory safety issues
        // of the `Vec` version. The data is just plain bytes.
        // Because the range removal happens in `Drop`, if the `Drain` iterator is leaked,
        // the removal will not happen.
        let Range { start, end } = crate::slice::range(range, ..self.len());
        assert!(self.is_char_boundary(start));
        assert!(self.is_char_boundary(end));

        // Take out two simultaneous borrows. The &mut String won't be accessed
        // until iteration is over, in Drop.
        let self_ptr = self as *mut _;
        // SAFETY: `slice::range` and `is_char_boundary` do the appropriate bounds checks.
        let chars_iter = unsafe { self.get_unchecked(start..end) }.chars();

        Drain {
            start,
            end,
            iter: chars_iter,
            string: self_ptr,
        }
    }
}

impl<const N: usize> String<N> {
    /// Constructs a new, empty `String` with a fixed capacity of `N` bytes.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    ///
    /// // allocate the string on the stack
    /// let mut s: String<4> = String::new();
    ///
    /// // allocate the string in a static variable
    /// static mut S: String<4> = String::new();
    /// ```
    #[inline]
    pub const fn new() -> Self {
        Self { vec: Vec::new() }
    }

    /// Decodes a UTF-16–encoded slice `v` into a `String`, returning [`Err`]
    /// if `v` contains any invalid data.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    ///
    /// // 𝄞music
    /// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075, 0x0073, 0x0069, 0x0063];
    /// let s: String<10> = String::from_utf16(v).unwrap();
    /// assert_eq!(s, "𝄞music");
    ///
    /// // 𝄞mu<invalid>ic
    /// let v = &[0xD834, 0xDD1E, 0x006d, 0x0075, 0xD800, 0x0069, 0x0063];
    /// assert!(String::<10>::from_utf16(v).is_err());
    /// ```
    #[inline]
    pub fn from_utf16(v: &[u16]) -> Result<Self, FromUtf16Error> {
        let mut s = Self::new();

        for c in char::decode_utf16(v.iter().cloned()) {
            match c {
                Ok(c) => {
                    s.push(c).map_err(|_| FromUtf16Error::Capacity)?;
                }
                Err(err) => {
                    return Err(FromUtf16Error::DecodeUtf16Error(err));
                }
            }
        }

        Ok(s)
    }

    /// Convert UTF-8 bytes into a `String`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::{String, Vec};
    ///
    /// let mut sparkle_heart = Vec::<u8, 4>::new();
    /// sparkle_heart.extend_from_slice(&[240, 159, 146, 150]);
    ///
    /// let sparkle_heart: String<4> = String::from_utf8(sparkle_heart)?;
    /// assert_eq!("💖", sparkle_heart);
    /// # Ok::<(), core::str::Utf8Error>(())
    /// ```
    ///
    /// Invalid UTF-8:
    ///
    /// ```
    /// use core::str::Utf8Error;
    /// use heapless::{String, Vec};
    ///
    /// let mut vec = Vec::<u8, 4>::new();
    /// vec.extend_from_slice(&[0, 159, 146, 150]);
    ///
    /// let e: Utf8Error = String::from_utf8(vec).unwrap_err();
    /// assert_eq!(e.valid_up_to(), 1);
    /// # Ok::<(), core::str::Utf8Error>(())
    /// ```
    #[inline]
    pub fn from_utf8(vec: Vec<u8, N>) -> Result<Self, Utf8Error> {
        core::str::from_utf8(&vec)?;
        Ok(Self { vec })
    }

    /// Convert UTF-8 bytes into a `String`, without checking that the string
    /// contains valid UTF-8.
    ///
    /// # Safety
    ///
    /// The bytes passed in must be valid UTF-8.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::{String, Vec};
    ///
    /// let mut sparkle_heart = Vec::<u8, 4>::new();
    /// sparkle_heart.extend_from_slice(&[240, 159, 146, 150]);
    ///
    /// // Safety: `sparkle_heart` Vec is known to contain valid UTF-8
    /// let sparkle_heart: String<4> = unsafe { String::from_utf8_unchecked(sparkle_heart) };
    /// assert_eq!("💖", sparkle_heart);
    /// ```
    #[inline]
    pub unsafe fn from_utf8_unchecked(vec: Vec<u8, N>) -> Self {
        Self { vec }
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
    /// let s: String<4> = String::try_from("ab")?;
    /// let b = s.into_bytes();
    /// assert!(b.len() == 2);
    ///
    /// assert_eq!(&[b'a', b'b'], &b[..]);
    /// # Ok::<(), ()>(())
    /// ```
    #[inline]
    pub fn into_bytes(self) -> Vec<u8, N> {
        self.vec
    }

    /// Get a reference to the `String`, erasing the `N` const-generic.
    ///
    ///
    /// ```rust
    /// # use heapless::string::{String, StringView};
    /// let s: String<10> = String::try_from("hello").unwrap();
    /// let view: &StringView = s.as_view();
    /// ```
    ///
    /// It is often preferable to do the same through type coerction, since `String<N>` implements `Unsize<StringView>`:
    ///
    /// ```rust
    /// # use heapless::string::{String, StringView};
    /// let s: String<10> = String::try_from("hello").unwrap();
    /// let view: &StringView = &s;
    /// ```
    #[inline]
    pub fn as_view(&self) -> &StringView {
        self
    }

    /// Get a mutable reference to the `String`, erasing the `N` const-generic.
    ///
    ///
    /// ```rust
    /// # use heapless::string::{String, StringView};
    /// let mut s: String<10> = String::try_from("hello").unwrap();
    /// let view: &mut StringView = s.as_mut_view();
    /// ```
    ///
    /// It is often preferable to do the same through type coerction, since `String<N>` implements `Unsize<StringView>`:
    ///
    /// ```rust
    /// # use heapless::string::{String, StringView};
    /// let mut s: String<10> = String::try_from("hello").unwrap();
    /// let view: &mut StringView = &mut s;
    /// ```
    #[inline]
    pub fn as_mut_view(&mut self) -> &mut StringView {
        self
    }

    /// Removes the specified range from the string in bulk, returning all
    /// removed characters as an iterator.
    ///
    /// The returned iterator keeps a mutable borrow on the string to optimize
    /// its implementation.
    ///
    /// # Panics
    ///
    /// Panics if the starting point or end point do not lie on a [`char`]
    /// boundary, or if they're out of bounds.
    ///
    /// # Leaking
    ///
    /// If the returned iterator goes out of scope without being dropped (due to
    /// [`core::mem::forget`], for example), the string may still contain a copy
    /// of any drained characters, or may have lost characters arbitrarily,
    /// including characters outside the range.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::String;
    ///
    /// let mut s = String::<32>::try_from("α is alpha, β is beta").unwrap();
    /// let beta_offset = s.find('β').unwrap_or(s.len());
    ///
    /// // Remove the range up until the β from the string
    /// let t: String<32> = s.drain(..beta_offset).collect();
    /// assert_eq!(t, "α is alpha, ");
    /// assert_eq!(s, "β is beta");
    ///
    /// // A full range clears the string, like `clear()` does
    /// s.drain(..);
    /// assert_eq!(s, "");
    /// ```
    pub fn drain<R>(&mut self, range: R) -> Drain<'_>
    where
        R: RangeBounds<usize>,
    {
        self.as_mut_view().drain(range)
    }
}

impl<S: Storage> StringInner<S> {
    /// Extracts a string slice containing the entire string.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    ///
    /// let mut s: String<4> = String::try_from("ab")?;
    /// assert!(s.as_str() == "ab");
    ///
    /// let _s = s.as_str();
    /// // s.push('c'); // <- cannot borrow `s` as mutable because it is also borrowed as immutable
    /// # Ok::<(), ()>(())
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
    /// let mut s: String<4> = String::try_from("ab")?;
    /// let s = s.as_mut_str();
    /// s.make_ascii_uppercase();
    /// # Ok::<(), ()>(())
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
    /// use heapless::String;
    ///
    /// let mut s: String<8> = String::try_from("hello")?;
    ///
    /// unsafe {
    ///     let vec = s.as_mut_vec();
    ///     assert_eq!(&[104, 101, 108, 108, 111][..], &vec[..]);
    ///
    ///     vec.reverse();
    /// }
    /// assert_eq!(s, "olleh");
    /// # Ok::<(), ()>(())
    /// ```
    pub unsafe fn as_mut_vec(&mut self) -> &mut VecInner<u8, S> {
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
    /// let mut s: String<8> = String::try_from("foo")?;
    ///
    /// assert!(s.push_str("bar").is_ok());
    ///
    /// assert_eq!("foobar", s);
    ///
    /// assert!(s.push_str("tender").is_err());
    /// # Ok::<(), ()>(())
    /// ```
    #[inline]
    #[allow(clippy::result_unit_err)]
    pub fn push_str(&mut self, string: &str) -> Result<(), ()> {
        self.vec.extend_from_slice(string.as_bytes())
    }

    /// Returns the maximum number of elements the String can hold.
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
        self.vec.storage_capacity()
    }

    /// Appends the given [`char`] to the end of this `String`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    ///
    /// let mut s: String<8> = String::try_from("abc")?;
    ///
    /// s.push('1').unwrap();
    /// s.push('2').unwrap();
    /// s.push('3').unwrap();
    ///
    /// assert!("abc123" == s.as_str());
    ///
    /// assert_eq!("abc123", s);
    /// # Ok::<(), ()>(())
    /// ```
    #[inline]
    #[allow(clippy::result_unit_err)]
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
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    ///
    /// let mut s: String<8> = String::try_from("hello")?;
    ///
    /// s.truncate(2);
    ///
    /// assert_eq!("he", s);
    /// # Ok::<(), ()>(())
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
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    ///
    /// let mut s: String<8> = String::try_from("foo")?;
    ///
    /// assert_eq!(s.pop(), Some('o'));
    /// assert_eq!(s.pop(), Some('o'));
    /// assert_eq!(s.pop(), Some('f'));
    ///
    /// assert_eq!(s.pop(), None);
    /// Ok::<(), ()>(())
    /// ```
    pub fn pop(&mut self) -> Option<char> {
        let ch = self.chars().next_back()?;

        // pop bytes that correspond to `ch`
        for _ in 0..ch.len_utf8() {
            unsafe {
                self.vec.pop_unchecked();
            }
        }

        Some(ch)
    }

    /// Removes a [`char`] from this `String` at a byte position and returns it.
    ///
    /// Note: Because this shifts over the remaining elements, it has a
    /// worst-case performance of *O*(n).
    ///
    /// # Panics
    ///
    /// Panics if `idx` is larger than or equal to the `String`'s length,
    /// or if it does not lie on a [`char`] boundary.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::String;
    ///
    /// let mut s: String<8> = String::try_from("foo").unwrap();
    ///
    /// assert_eq!(s.remove(0), 'f');
    /// assert_eq!(s.remove(1), 'o');
    /// assert_eq!(s.remove(0), 'o');
    /// ```
    #[inline]
    pub fn remove(&mut self, index: usize) -> char {
        let ch = match self[index..].chars().next() {
            Some(ch) => ch,
            None => panic!("cannot remove a char from the end of a string"),
        };

        let next = index + ch.len_utf8();
        let len = self.len();
        let ptr = self.vec.as_mut_ptr();
        unsafe {
            core::ptr::copy(ptr.add(next), ptr.add(index), len - next);
            self.vec.set_len(len - (next - index));
        }
        ch
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
    /// let mut s: String<8> = String::try_from("foo")?;
    ///
    /// s.clear();
    ///
    /// assert!(s.is_empty());
    /// assert_eq!(0, s.len());
    /// assert_eq!(8, s.capacity());
    /// Ok::<(), ()>(())
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.vec.clear()
    }
}

impl<const N: usize> Default for String<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, const N: usize> TryFrom<&'a str> for String<N> {
    type Error = ();
    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        let mut new = String::new();
        new.push_str(s)?;
        Ok(new)
    }
}

impl<const N: usize> str::FromStr for String<N> {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut new = String::new();
        new.push_str(s)?;
        Ok(new)
    }
}

impl<const N: usize> iter::FromIterator<char> for String<N> {
    fn from_iter<T: IntoIterator<Item = char>>(iter: T) -> Self {
        let mut new = String::new();
        for c in iter {
            new.push(c).unwrap();
        }
        new
    }
}

impl<'a, const N: usize> iter::FromIterator<&'a char> for String<N> {
    fn from_iter<T: IntoIterator<Item = &'a char>>(iter: T) -> Self {
        let mut new = String::new();
        for c in iter {
            new.push(*c).unwrap();
        }
        new
    }
}

impl<'a, const N: usize> iter::FromIterator<&'a str> for String<N> {
    fn from_iter<T: IntoIterator<Item = &'a str>>(iter: T) -> Self {
        let mut new = String::new();
        for c in iter {
            new.push_str(c).unwrap();
        }
        new
    }
}

impl<const N: usize> Clone for String<N> {
    fn clone(&self) -> Self {
        Self {
            vec: self.vec.clone(),
        }
    }
}

impl<S: Storage> fmt::Debug for StringInner<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <str as fmt::Debug>::fmt(self, f)
    }
}

impl<S: Storage> fmt::Display for StringInner<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <str as fmt::Display>::fmt(self, f)
    }
}

impl<S: Storage> hash::Hash for StringInner<S> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, hasher: &mut H) {
        <str as hash::Hash>::hash(self, hasher)
    }
}

impl<S: Storage> fmt::Write for StringInner<S> {
    fn write_str(&mut self, s: &str) -> Result<(), fmt::Error> {
        self.push_str(s).map_err(|_| fmt::Error)
    }

    fn write_char(&mut self, c: char) -> Result<(), fmt::Error> {
        self.push(c).map_err(|_| fmt::Error)
    }
}

impl<S: Storage> ops::Deref for StringInner<S> {
    type Target = str;

    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl<S: Storage> ops::DerefMut for StringInner<S> {
    fn deref_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl<S: Storage> borrow::Borrow<str> for StringInner<S> {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}
impl<S: Storage> borrow::BorrowMut<str> for StringInner<S> {
    fn borrow_mut(&mut self) -> &mut str {
        self.as_mut_str()
    }
}

impl<S: Storage> AsRef<str> for StringInner<S> {
    #[inline]
    fn as_ref(&self) -> &str {
        self
    }
}

impl<S: Storage> AsRef<[u8]> for StringInner<S> {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

impl<S1: Storage, S2: Storage> PartialEq<StringInner<S1>> for StringInner<S2> {
    fn eq(&self, rhs: &StringInner<S1>) -> bool {
        str::eq(&**self, &**rhs)
    }
}

// String<N> == str
impl<S: Storage> PartialEq<str> for StringInner<S> {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        str::eq(self, other)
    }
}

// String<N> == &'str
impl<S: Storage> PartialEq<&str> for StringInner<S> {
    #[inline]
    fn eq(&self, other: &&str) -> bool {
        str::eq(self, &other[..])
    }
}

// str == String<N>
impl<S: Storage> PartialEq<StringInner<S>> for str {
    #[inline]
    fn eq(&self, other: &StringInner<S>) -> bool {
        str::eq(self, &other[..])
    }
}

// &'str == String<N>
impl<S: Storage> PartialEq<StringInner<S>> for &str {
    #[inline]
    fn eq(&self, other: &StringInner<S>) -> bool {
        str::eq(self, &other[..])
    }
}

impl<S: Storage> Eq for StringInner<S> {}

impl<S1: Storage, S2: Storage> PartialOrd<StringInner<S1>> for StringInner<S2> {
    #[inline]
    fn partial_cmp(&self, other: &StringInner<S1>) -> Option<Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }
}

impl<S: Storage> Ord for StringInner<S> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        Ord::cmp(&**self, &**other)
    }
}

/// Equivalent to [`format`](https://doc.rust-lang.org/std/fmt/fn.format.html).
///
/// Please note that using [`format!`] might be preferable.
///
/// # Errors
///
/// There are two possible error cases. Both return the unit type [`core::fmt::Error`].
///
/// - In case the formatting exceeds the string's capacity. This error does not exist in
/// the standard library as the string would just grow.
/// - If a formatting trait implementation returns an error. The standard library panics
/// in this case.
///
/// [`format!`]: crate::format!
#[doc(hidden)]
pub fn format<const N: usize>(args: Arguments<'_>) -> Result<String<N>, fmt::Error> {
    fn format_inner<const N: usize>(args: Arguments<'_>) -> Result<String<N>, fmt::Error> {
        let mut output = String::new();
        output.write_fmt(args)?;
        Ok(output)
    }

    args.as_str().map_or_else(
        || format_inner(args),
        |s| s.try_into().map_err(|_| fmt::Error),
    )
}

/// Macro that creates a fixed capacity [`String`]. Equivalent to [`format!`](https://doc.rust-lang.org/std/macro.format.html).
///
/// The macro's arguments work in the same way as the regular macro.
///
/// It is possible to explicitly specify the capacity of the returned string as the first argument.
/// In this case it is necessary to disambiguate by separating the capacity with a semicolon.
///
/// # Errors
///
/// There are two possible error cases. Both return the unit type [`core::fmt::Error`].
///
/// - In case the formatting exceeds the string's capacity. This error does not exist in
/// the standard library as the string would just grow.
/// - If a formatting trait implementation returns an error. The standard library panics
/// in this case.
///
/// # Examples
///
/// ```
/// # fn main() -> Result<(), core::fmt::Error> {
/// use heapless::{format, String};
///
/// // Notice semicolon instead of comma!
/// format!(4; "test")?;
/// format!(15; "hello {}", "world!")?;
/// format!(20; "x = {}, y = {y}", 10, y = 30)?;
/// let (x, y) = (1, 2);
/// format!(12; "{x} + {y} = 3")?;
///
/// let implicit: String<10> = format!("speed = {}", 7)?;
/// # Ok(())
/// # }
/// ```
#[macro_export]
macro_rules! format {
    // Without semicolon as separator to disambiguate between arms, Rust just
    // chooses the first so that the format string would land in $max.
    ($max:expr; $($arg:tt)*) => {{
        let res = $crate::_export::format::<$max>(core::format_args!($($arg)*));
        res
    }};
    ($($arg:tt)*) => {{
        let res = $crate::_export::format(core::format_args!($($arg)*));
        res
    }};
}

macro_rules! impl_try_from_num {
    ($num:ty, $size:expr) => {
        impl<const N: usize> core::convert::TryFrom<$num> for String<N> {
            type Error = ();
            fn try_from(s: $num) -> Result<Self, Self::Error> {
                let mut new = String::new();
                write!(&mut new, "{}", s).map_err(|_| ())?;
                Ok(new)
            }
        }
    };
}

impl_try_from_num!(i8, 4);
impl_try_from_num!(i16, 6);
impl_try_from_num!(i32, 11);
impl_try_from_num!(i64, 20);

impl_try_from_num!(u8, 3);
impl_try_from_num!(u16, 5);
impl_try_from_num!(u32, 10);
impl_try_from_num!(u64, 20);

#[cfg(test)]
mod tests {
    use crate::{String, Vec};

    #[test]
    fn static_new() {
        static mut _S: String<8> = String::new();
    }

    #[test]
    fn clone() {
        let s1: String<20> = String::try_from("abcd").unwrap();
        let mut s2 = s1.clone();
        s2.push_str(" efgh").unwrap();

        assert_eq!(s1, "abcd");
        assert_eq!(s2, "abcd efgh");
    }

    #[test]
    fn cmp() {
        let s1: String<4> = String::try_from("abcd").unwrap();
        let s2: String<4> = String::try_from("zzzz").unwrap();

        assert!(s1 < s2);
    }

    #[test]
    fn cmp_heterogenous_size() {
        let s1: String<4> = String::try_from("abcd").unwrap();
        let s2: String<8> = String::try_from("zzzz").unwrap();

        assert!(s1 < s2);
    }

    #[test]
    fn debug() {
        use core::fmt::Write;

        let s: String<8> = String::try_from("abcd").unwrap();
        let mut std_s = std::string::String::new();
        write!(std_s, "{:?}", s).unwrap();
        assert_eq!("\"abcd\"", std_s);
    }

    #[test]
    fn display() {
        use core::fmt::Write;

        let s: String<8> = String::try_from("abcd").unwrap();
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
    fn try_from() {
        let s: String<4> = String::try_from("123").unwrap();
        assert!(s.len() == 3);
        assert_eq!(s, "123");

        let _: () = String::<2>::try_from("123").unwrap_err();
    }

    #[test]
    fn from_str() {
        use core::str::FromStr;

        let s: String<4> = String::<4>::from_str("123").unwrap();
        assert!(s.len() == 3);
        assert_eq!(s, "123");

        let _: () = String::<2>::from_str("123").unwrap_err();
    }

    #[test]
    fn from_iter() {
        let mut v: Vec<char, 5> = Vec::new();
        v.push('h').unwrap();
        v.push('e').unwrap();
        v.push('l').unwrap();
        v.push('l').unwrap();
        v.push('o').unwrap();
        let string1: String<5> = v.iter().collect(); //&char
        let string2: String<5> = "hello".chars().collect(); //char
        assert_eq!(string1, "hello");
        assert_eq!(string2, "hello");
    }

    #[test]
    #[should_panic]
    fn from_panic() {
        let _: String<4> = String::try_from("12345").unwrap();
    }

    #[test]
    fn try_from_num() {
        let v: String<20> = String::try_from(18446744073709551615_u64).unwrap();
        assert_eq!(v, "18446744073709551615");

        let _: () = String::<2>::try_from(18446744073709551615_u64).unwrap_err();
    }

    #[test]
    fn into_bytes() {
        let s: String<4> = String::try_from("ab").unwrap();
        let b: Vec<u8, 4> = s.into_bytes();
        assert_eq!(b.len(), 2);
        assert_eq!(&[b'a', b'b'], &b[..]);
    }

    #[test]
    fn as_str() {
        let s: String<4> = String::try_from("ab").unwrap();

        assert_eq!(s.as_str(), "ab");
        // should be moved to fail test
        //    let _s = s.as_str();
        // s.push('c'); // <- cannot borrow `s` as mutable because it is also borrowed as immutable
    }

    #[test]
    fn as_mut_str() {
        let mut s: String<4> = String::try_from("ab").unwrap();
        let s = s.as_mut_str();
        s.make_ascii_uppercase();
        assert_eq!(s, "AB");
    }

    #[test]
    fn push_str() {
        let mut s: String<8> = String::try_from("foo").unwrap();
        assert!(s.push_str("bar").is_ok());
        assert_eq!("foobar", s);
        assert_eq!(s, "foobar");
        assert!(s.push_str("tender").is_err());
        assert_eq!("foobar", s);
        assert_eq!(s, "foobar");
    }

    #[test]
    fn push() {
        let mut s: String<6> = String::try_from("abc").unwrap();
        assert!(s.push('1').is_ok());
        assert!(s.push('2').is_ok());
        assert!(s.push('3').is_ok());
        assert!(s.push('4').is_err());
        assert!("abc123" == s.as_str());
    }

    #[test]
    fn as_bytes() {
        let s: String<8> = String::try_from("hello").unwrap();
        assert_eq!(&[104, 101, 108, 108, 111], s.as_bytes());
    }

    #[test]
    fn truncate() {
        let mut s: String<8> = String::try_from("hello").unwrap();
        s.truncate(6);
        assert_eq!(s.len(), 5);
        s.truncate(2);
        assert_eq!(s.len(), 2);
        assert_eq!("he", s);
        assert_eq!(s, "he");
    }

    #[test]
    fn pop() {
        let mut s: String<8> = String::try_from("foo").unwrap();
        assert_eq!(s.pop(), Some('o'));
        assert_eq!(s.pop(), Some('o'));
        assert_eq!(s.pop(), Some('f'));
        assert_eq!(s.pop(), None);
    }

    #[test]
    fn pop_uenc() {
        let mut s: String<8> = String::try_from("é").unwrap();
        assert_eq!(s.len(), 3);
        match s.pop() {
            Some(c) => {
                assert_eq!(s.len(), 1);
                assert_eq!(c, '\u{0301}'); // accute accent of e
            }
            None => panic!(),
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
        let mut s: String<8> = String::try_from("foo").unwrap();
        s.clear();
        assert!(s.is_empty());
        assert_eq!(0, s.len());
        assert_eq!(8, s.capacity());
    }

    #[test]
    fn remove() {
        let mut s: String<8> = String::try_from("foo").unwrap();
        assert_eq!(s.remove(0), 'f');
        assert_eq!(s.as_str(), "oo");
    }

    #[test]
    fn remove_uenc() {
        let mut s: String<8> = String::try_from("ĝėēƶ").unwrap();
        assert_eq!(s.remove(2), 'ė');
        assert_eq!(s.remove(2), 'ē');
        assert_eq!(s.remove(2), 'ƶ');
        assert_eq!(s.as_str(), "ĝ");
    }

    #[test]
    fn remove_uenc_combo_characters() {
        let mut s: String<8> = String::try_from("héy").unwrap();
        assert_eq!(s.remove(2), '\u{0301}');
        assert_eq!(s.as_str(), "hey");
    }

    #[test]
    fn format() {
        let number = 5;
        let float = 3.12;
        let formatted = format!(15; "{:0>3} plus {float}", number).unwrap();
        assert_eq!(formatted, "005 plus 3.12")
    }
    #[test]
    fn format_inferred_capacity() {
        let number = 5;
        let float = 3.12;
        let formatted: String<15> = format!("{:0>3} plus {float}", number).unwrap();
        assert_eq!(formatted, "005 plus 3.12")
    }

    #[test]
    fn format_overflow() {
        let i = 1234567;
        let formatted = format!(4; "13{}", i);
        assert_eq!(formatted, Err(core::fmt::Error))
    }

    #[test]
    fn format_plain_string_overflow() {
        let formatted = format!(2; "123");
        assert_eq!(formatted, Err(core::fmt::Error))
    }
}

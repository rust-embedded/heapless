//! A fixed capacity [`CString`](https://doc.rust-lang.org/std/ffi/struct.CString.html).

use crate::{vec::Vec, CapacityError};
use core::{
    ffi::{c_char, CStr},
    ops::Deref,
};

/// A fixed capacity [`CString`](https://doc.rust-lang.org/std/ffi/struct.CString.html).
///
/// It stores up to `N - 1` non-nul characters with a trailing nul terminator.
#[derive(Clone, Default)]
pub struct CString<const N: usize> {
    inner: Vec<u8, N>,
}

/// Naive implementation for `memchr`.
///
/// TODO Consider using [the `memchr` crate](https://github.com/BurntSushi/memchr), which
/// provides a heavily optimized `memchr` function.
fn memchr(needle: u8, haystack: &[u8]) -> Option<usize> {
    haystack.iter().position(|&byte| byte == needle)
}

impl<const N: usize> CString<N> {
    /// Creates a new C-compatible string with a terminating nul byte.
    ///
    /// ```rust
    /// use core::ffi::CStr;
    /// use heapless::CString;
    ///
    /// // A fixed-size `CString` that can store up to 10 characters
    /// // including the nul terminator
    /// let empty = CString::<10>::new();
    ///
    /// assert_eq!(empty.as_c_str(), <&CStr>::default());
    /// assert_eq!(empty.to_str(), Ok(""));
    /// ```
    pub fn new() -> Self {
        const {
            assert!(N > 0);
        }

        let mut inner = Vec::new();

        // SAFETY: We just asserted that `N > 0`.
        unsafe { inner.push_unchecked(b'\0') };

        Self { inner }
    }

    /// Unsafely creates a [`CString`] from a byte slice.
    ///
    /// This function will copy the provided `bytes` to a [`CString`] without
    /// performing any sanity checks.
    ///
    /// The function will fail if `bytes.len() > N`.
    ///
    /// # Safety
    ///
    /// The provided slice **must** be nul-terminated and not contain any interior
    /// nul bytes.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use heapless::CString;
    /// let mut cstr = unsafe { CString::<5>::from_bytes_with_nul_unchecked(b"cstr\0").unwrap() };
    ///
    /// assert_eq!(cstr.to_str(), Ok("cstr"));
    /// ```
    pub unsafe fn from_bytes_with_nul_unchecked(bytes: &[u8]) -> Result<Self, CapacityError> {
        let mut inner = Vec::new();

        inner.extend_from_slice(bytes)?;

        Ok(Self { inner })
    }

    /// Instantiates a [`CString`] copying from the giving byte slice, assuming it is
    /// nul-terminated.
    ///
    /// Fails if the given byte slice has any interior nul byte, if the slice does not
    /// end with a nul byte, or if the byte slice can't fit in `N`.
    pub fn from_bytes_with_nul(bytes: &[u8]) -> Result<Self, CapacityError> {
        let mut string = Self::new();

        string.push_bytes(bytes)?;

        Ok(string)
    }

    /// Builds a [`CString`] copying from a raw C string pointer.
    ///
    /// # Safety
    ///
    /// - The memory pointed to by `ptr` must contain a valid nul terminator at the
    ///   end of the string.
    /// - `ptr` must be valid for reads of bytes up to and including the nul terminator.
    ///   This means in particular:
    ///     - The entire memory range of this `CStr` must be contained within a single allocated object!
    ///     - `ptr` must be non-nul even for a zero-length `CStr`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use core::ffi::{c_char, CStr};
    /// use heapless::CString;
    ///
    /// const HELLO_PTR: *const c_char = {
    ///     const BYTES: &[u8] = b"Hello, world!\0";
    ///     BYTES.as_ptr().cast()
    /// };
    ///
    /// let copied = unsafe { CString::<14>::from_raw(HELLO_PTR) }.unwrap();
    ///
    /// assert_eq!(copied.to_str(), Ok("Hello, world!"));
    /// ```
    pub unsafe fn from_raw(ptr: *const c_char) -> Result<Self, CapacityError> {
        // SAFETY: The given pointer to a string is assumed to be nul-terminated.
        Self::from_bytes_with_nul(unsafe { CStr::from_ptr(ptr).to_bytes_with_nul() })
    }

    /// Converts the [`CString`] to a [`CStr`] slice.
    pub fn as_c_str(&self) -> &CStr {
        debug_assert!(CStr::from_bytes_with_nul(&self.inner).is_ok());

        unsafe { CStr::from_bytes_with_nul_unchecked(&self.inner) }
    }

    /// Calculates the length of `self.inner` would have if it appended `bytes`.
    fn capacity_with_bytes(&self, bytes: &[u8]) -> Option<usize> {
        match bytes.last() {
            None => None,
            Some(0) if bytes.len() < 2 => None,
            Some(0) => {
                // `bytes` is nul-terminated and so is `self.inner`.
                // Adding up both would account for 2 nul bytes when only a single byte
                // would end up in the resulting CString.
                Some(self.inner.len() + bytes.len() - 1)
            }
            Some(_) => {
                // No terminating nul byte in `bytes` but there's one in
                // `self.inner`, so the math lines up nicely.
                //
                // In the case that `bytes` has a nul byte anywhere else, we would
                // error after `memchr` is called. So there's no problem.
                Some(self.inner.len() + bytes.len())
            }
        }
    }

    /// Extends the [`CString`] with the given bytes.
    ///
    /// This function fails if the [`CString`] would not have enough capacity to append the bytes or
    /// if the bytes contain an interior nul byte.
    ///
    /// # Example
    ///
    /// ```rust
    /// use heapless::CString;
    ///
    /// let mut cstr = CString::<10>::new();
    ///
    /// cstr.push_bytes(b"hey").unwrap();
    /// cstr.push_bytes(b" there\0").unwrap();
    ///
    /// assert_eq!(cstr.to_str(), Ok("hey there"));
    /// ```
    pub fn push_bytes(&mut self, bytes: &[u8]) -> Result<(), CapacityError> {
        let Some(capacity) = self.capacity_with_bytes(bytes) else {
            return Ok(());
        };

        if capacity > N {
            // Cannot store these bytes due to an insufficient capacity.
            return Err(CapacityError);
        }

        match memchr(0, bytes) {
            Some(index) if index + 1 == bytes.len() => {
                // SAFETY: A string is left in a valid state because appended bytes are nul-terminated.
                unsafe { self.extend_from_slice(bytes) }?;

                Ok(())
            }
            Some(_) => {
                // Found an interior nul byte
                Err(CapacityError)
            }
            None => {
                // Because given bytes has no nul byte anywhere, we insert the bytes and
                // then add the nul byte terminator.
                //
                // We've ensured above that we have enough space left to insert these bytes,
                // so the operations below must succeed.
                //
                // SAFETY: We append a missing nul terminator right below.
                unsafe {
                    self.extend_from_slice(bytes).unwrap();
                    self.inner.push_unchecked(0);
                };

                Ok(())
            }
        }
    }

    /// Removes the nul byte terminator from the inner buffer.
    ///
    /// # Safety
    ///
    /// Callers must ensure to add the nul terminator back after this function is called.
    #[inline]
    unsafe fn pop_terminator(&mut self) {
        debug_assert_eq!(self.inner.last(), Some(&0));

        // SAFETY: We always have the nul terminator at the end.
        unsafe { self.inner.pop_unchecked() };
    }

    /// Removes the existing nul terminator and then extends `self` with the given bytes.
    ///
    /// # Safety
    ///
    /// If `additional` is not nul-terminated, the [`CString`] is left non nul-terminated, which is
    /// an invalid state. Caller must ensure that either `additional` has a terminating nul byte
    /// or ensure to append a trailing null terminator.
    unsafe fn extend_from_slice(&mut self, additional: &[u8]) -> Result<(), CapacityError> {
        self.pop_terminator();

        self.inner.extend_from_slice(additional)
    }

    /// Returns the underlying byte slice including the trailing nul terminator.
    ///
    /// # Example
    ///
    /// ```rust
    /// use heapless::CString;
    ///
    /// let mut cstr = CString::<5>::new();
    /// cstr.push_bytes(b"abc").unwrap();
    ///
    /// assert_eq!(cstr.as_bytes_with_nul(), b"abc\0");
    /// ```
    #[inline]
    pub fn as_bytes_with_nul(&self) -> &[u8] {
        &self.inner
    }

    /// Returns the underlying byte slice excluding the trailing nul terminator.
    ///
    /// # Example
    ///
    /// ```rust
    /// use heapless::CString;
    ///
    /// let mut cstr = CString::<5>::new();
    /// cstr.push_bytes(b"abc").unwrap();
    ///
    /// assert_eq!(cstr.as_bytes(), b"abc");
    /// ```
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        debug_assert_eq!(self.inner.last().copied(), Some(0));

        &self.inner[..self.inner.len() - 1]
    }
}

impl<const N: usize> Deref for CString<N> {
    type Target = CStr;

    fn deref(&self) -> &Self::Target {
        self.as_c_str()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty() {
        let empty = CString::<1>::new();

        assert_eq!(empty.as_c_str(), <&CStr>::default());
        assert_eq!(empty.as_bytes(), &[]);
        assert_eq!(empty.to_str(), Ok(""));
    }

    #[test]
    fn push_no_bytes() {
        let mut cstr = CString::<1>::new();

        cstr.push_bytes(b"").unwrap();
    }

    #[test]
    fn push_bytes() {
        let mut cstr = CString::<11>::new();
        assert_eq!(cstr.to_str(), Ok(""));

        cstr.push_bytes(b"hello").unwrap();

        assert_eq!(cstr.to_str(), Ok("hello"));

        // Call must fail since `w\0rld` contains an interior nul byte.
        assert!(cstr.push_bytes(b"w\0rld").is_err());

        // However, the call above _must not_ have invalidated the state of our CString
        assert_eq!(cstr.to_str(), Ok("hello"));

        // Call must fail since we can't store "hello world\0" in 11 bytes
        assert!(cstr.push_bytes(b" world").is_err());

        // Yet again, the call above must not have invalidated the state of our CString
        // (as it would e.g. if we pushed the bytes but then failed to push the nul terminator)
        assert_eq!(cstr.to_str(), Ok("hello"));

        assert!(cstr.push_bytes(b" Bill").is_ok());

        assert_eq!(cstr.to_str(), Ok("hello Bill"));
    }

    #[test]
    fn calculate_capacity_with_additional_bytes() {
        const INITIAL_BYTES: &[u8] = b"abc";

        let mut cstr = CString::<5>::new();

        cstr.push_bytes(INITIAL_BYTES).unwrap();

        assert_eq!(cstr.to_bytes_with_nul().len(), 4);
        assert_eq!(cstr.capacity_with_bytes(b""), None);
        assert_eq!(cstr.capacity_with_bytes(b"\0"), None);
        assert_eq!(
            cstr.capacity_with_bytes(b"d"),
            Some(INITIAL_BYTES.len() + 2)
        );
        assert_eq!(
            cstr.capacity_with_bytes(b"d\0"),
            Some(INITIAL_BYTES.len() + 2)
        );
        assert_eq!(
            cstr.capacity_with_bytes(b"defg"),
            Some(INITIAL_BYTES.len() + 5)
        );
        assert_eq!(
            cstr.capacity_with_bytes(b"defg\0"),
            Some(INITIAL_BYTES.len() + 5)
        );
    }

    #[test]
    fn dereference_into_c_str() {
        assert_eq!(CString::<1>::new().deref(), <&CStr>::default());
        assert_eq!(CString::<2>::new().deref(), <&CStr>::default());
        assert_eq!(CString::<3>::new().deref(), <&CStr>::default());

        let mut string = CString::<2>::new();
        string.push_bytes(&[65]).unwrap();

        assert_eq!(string.deref(), c"A");

        let mut string = CString::<3>::new();
        string.push_bytes(&[65, 66]).unwrap();

        assert_eq!(string.deref(), c"AB");

        let mut string = CString::<4>::new();
        string.push_bytes(&[65, 66, 67]).unwrap();

        assert_eq!(string.deref(), c"ABC");
    }
}

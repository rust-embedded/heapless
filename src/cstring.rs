use core::ffi::{c_char, CStr};

/// A fixed capacity [`CString`](https://doc.rust-lang.org/std/ffi/struct.CString.html).
///
/// Stores up to N-1 elements with a byte reserved for the terminating nil byte.
#[derive(Clone)]
pub struct CString<const CAP: usize> {
    buf: crate::Vec<u8, CAP>,
}

/// Naive implementation for memchr
///
/// The naive implementation is somewhat competitive to libc's memchr or BurntSushi's optimized
/// implementation for tiny slices (as shown by https://gist.github.com/Alexhuszagh/f9929e7d8e0277aa1281f511a841a167),
/// which should be the average slice size for this crate due to its use case, but ideally we'd use at least BurntSushi's fallback implementation here.
fn memchr(needle: u8, haystack: &[u8]) -> Option<usize> {
    haystack.iter().position(|&b| b == needle)
}

impl<const CAP: usize> CString<CAP> {
    /// Constructs a new, "empty" `CString`.
    ///
    /// Stores the first nil byte as the first
    /// 
    /// ```
    /// use heapless::CString;
    /// use std::ffi::CStr;   
    ///
    /// // Fixed-size CString that can store up to 10 elements
    /// // (counting the nul terminator)
    /// let empty = CString::<10>::new();
    /// 
    /// assert_eq!(empty.as_cstr(), <&CStr>::default());
    /// assert_eq!(empty.to_str(), Ok(""));
    /// ```
    pub fn new() -> Self {
        crate::sealed::greater_than_0::<CAP>();

        let mut buf = crate::Vec::new();

        // Safety: will not fail since we const-assert that CAP > 0.
        unsafe { buf.push(0).unwrap_unchecked() };

        Self { buf }
    }

    /// Unsafely creates a [`CString`] from a byte slice.
    ///
    /// This function will copy the provided `bytes` to a [`CString`] without
    /// performing any sanity checks.
    ///
    /// The function will fail if `bytes.len() > CAP`.
    ///
    /// # Safety
    ///
    /// The provided slice **must** be nul-terminated and not contain any interior
    /// nul bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::CString;
    /// let mut cstr: CString<5> = unsafe {
    ///     CString::from_bytes_with_nul_unchecked(b"cstr\0").unwrap()
    /// };
    ///
    /// assert_eq!(cstr.to_str(), Ok("cstr"));
    /// ```
    pub unsafe fn from_bytes_with_nul_unchecked(bytes: &[u8]) -> Result<Self, ()> {
        let mut buf = crate::Vec::new();

        buf.extend_from_slice(bytes)?;

        Ok(Self { buf })
    }

    /// Instantiate a [`CString`] copying from the giving bytes, assuming it is
    /// null-terminated (ends with a single zero byte).
    /// 
    /// Fails if the given byte slice has any interior nul byte, if the slice does not
    /// end in a zero byte or if the byte slice can't fit in `CAP`.
    pub fn from_bytes_with_nul(bytes: &[u8]) -> Result<Self, ()> {
        let mut me = Self::new();

        me.push_bytes(bytes)?;

        Ok(me)
    }

    /// Builds a [`CString`] copying from a raw C string pointer.
    ///
    /// # Safety
    ///
    /// * The memory pointed to by `ptr` must contain a valid nul terminator at the
    ///   end of the string.
    ///
    /// * `ptr` must be valid for reads of bytes up to and including the null terminator.
    ///   This means in particular:
    ///
    ///     * The entire memory range of this `CStr` must be contained within a single allocated object!
    ///     * `ptr` must be non-null even for a zero-length cstr.
    ///
    /// # Example
    ///
    /// ```
    /// use std::ffi::{c_char, CStr};
    /// use heapless::CString;
    ///
    /// const HELLO_PTR: *const c_char = {
    ///     const BYTES: &[u8] = b"Hello, world!\0";
    ///     BYTES.as_ptr().cast()
    /// };
    ///
    /// let copied = unsafe {
    ///     CString::<14>::from_ptr(HELLO_PTR)
    /// }.unwrap();
    ///
    /// assert_eq!(copied.to_str(), Ok("Hello, world!"));
    /// ```
    pub unsafe fn from_ptr<'a>(ptr: *const c_char) -> Result<Self, ()> {
        let cstr = CStr::from_ptr(ptr).to_bytes_with_nul();

        Self::from_bytes_with_nul(cstr)
    }

    /// Converts the [`CString`] to a [`CStr`] slice. This always succeeds and is zero cost.
    pub fn as_cstr(&self) -> &CStr {
        if cfg!(debug_assertions) {
            // When in debug builds, ensure
            CStr::from_bytes_with_nul(&self.buf).unwrap()
        } else {
            unsafe { CStr::from_bytes_with_nul_unchecked(&self.buf) }
        }
    }

    /// How many bytes were inserted to this [`CString`] so far, considering its
    /// null terminator.
    ///
    /// Must always be bigger than zero, since even an empty [`CString`]
    /// ends in a zero byte.
    /// # Example
    ///
    /// ```
    /// use std::ffi::{c_char, CStr};
    /// use heapless::CString;
    ///
    /// // Length is one (null terminator only), capacity is 10
    /// let mut cstr = CString::<11>::new();
    ///
    /// // Insert 5 bytes to it
    /// cstr.push_bytes(b"/etc/").unwrap();
    /// // Length is 6 (5 bytes inserted plus nul terminator)
    /// assert_eq!(cstr.len(), 6);
    /// cstr.push_bytes(b"dconf").unwrap();
    ///
    /// assert_eq!(cstr.to_str(), Ok("/etc/dconf"));
    /// ```
    pub fn len(&self) -> usize {
        self.as_bytes_with_null().len()
    }

    /// Calculates the length `self.buf` would have if it appended `bytes`
    fn size_if_appended_bytes(&self, bytes: &[u8]) -> Option<usize> {
        match bytes.last() {
            Some(0) => {
                // `bytes` is null-terminated and so is `self.buf`.
                // Adding up both would account for 2 nul bytes when only a single byte
                // would end up in the resulting CString
                Some(self.buf.len() + bytes.len() - 1)
            }
            Some(_) => {
                // No terminating null byte in `bytes` but there's one in
                // `self.buf`, so the math lines up nicely.
                //
                // In the case that `bytes` has a nul byte anywhere else we'd
                // err after `memchr` is called, so there's no problem
                Some(self.buf.len() + bytes.len())
            }
            None => {
                // Nothing to insert so there'd be no change in size

                None
            }
        }
    }

    // pub fn push(&mut self, byte: u8) -> Result<(), ()> {

    // }

    /// Extends the [`CString`] with the given bytes.
    ///
    /// This method fails if the [`CString`] would not have enough capacity to append the bytes or
    /// if the bytes contain an interior nul byte (a zero byte not at the buffer's final position).
    ///
    /// If there's a nul byte at the end, however, the function does not fail.
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
    pub fn push_bytes(&mut self, bytes: &[u8]) -> Result<(), ()> {
        match self.size_if_appended_bytes(bytes) {
            Some(resulting_size) if resulting_size > CAP => {
                // Can't store these bytes due to insufficient capacity
                return Err(());
            }
            Some(_) => {}
            None => {
                // Nothing to insert
                assert!(false);
                return Ok(());
            }
        }

        match memchr(0, bytes) {
            Some(nul_pos) if nul_pos + 1 == bytes.len() => {
                // Safety: inserted bytes are null-terminated so
                //         the CString will be left in a valid state
                unsafe { self.extend_slice(bytes) }?;

                Ok(())
            }
            Some(_nul_pos) => {
                // Found an interior nul byte
                Err(())
            }
            None => {
                // Given bytes had no nul byte anywhere,
                // so we'll insert them and then add the nul byte terminator.

                // We've ensured above that we have enough space left to insert these bytes,
                // so the operations below must succeed

                // Safety: CString will not have a null terminator after this call is done,
                //         but we'll fix that right below
                unsafe { self.extend_slice(bytes) }.unwrap();

                // Add the nul byte terminator
                self.buf.push(0).map_err(|_| ()).unwrap();

                Ok(())
            }
        }
    }

    /// Removes the nil byte terminator from the inner buffer.
    ///
    /// # Safety: caller must ensure to re-add the terminator after this function is called
    #[inline]
    unsafe fn pop_terminator(&mut self) {
        if cfg!(debug_assertions) {
            let popped = self.buf.pop();

            assert_eq!(popped, Some(0));
        } else {
            unsafe { self.buf.pop_unchecked() };
        }
    }

    /// Converts this [`CString`] to a string slice if the [`CString`] represents valid UTF-8.
    ///
    /// # Example
    ///
    /// ```
    /// use heapless::CString;
    ///
    /// let mut cstr: CString<10> = CString::new();
    /// cstr.push_bytes(b"heapless").unwrap();
    ///
    /// assert_eq!(
    ///     cstr.to_str(),
    ///     Ok("heapless")
    /// );
    /// ```
    pub fn to_str(&self) -> Result<&str, core::str::Utf8Error> {
        core::str::from_utf8(self.inner_without_nil_terminator())
    }

    /// Converts a [`CString`] to a string slice without checking
    /// that the string contains valid UTF-8.
    ///
    /// See the safe version, [`CString::to_str`], for more information.
    ///
    /// # Safety
    ///
    /// The bytes passed in must be valid UTF-8.
    ///
    /// # Example
    ///
    /// ```
    /// use heapless::CString;
    ///
    /// let mut cstr: CString<10> = CString::new();
    /// cstr.push_bytes(b"heapless").unwrap();
    ///
    /// assert_eq!(
    ///     unsafe { cstr.as_str_unchecked() },
    ///     "heapless",
    /// );
    /// ```
    pub unsafe fn as_str_unchecked(&self) -> &str {
        core::str::from_utf8_unchecked(self.inner_without_nil_terminator())
    }

    /// Removes the existing nul terminator and then extends `self` with the given bytes.
    ///
    /// # Safety
    ///
    ///  If `additional` is not null-terminated, the CString is left non null-terminated, which is
    ///  an invalid state. Caller must ensure that either `additional` has a terminating nul byte
    ///  or ensure to fix the CString after calling `extend_slice`.
    unsafe fn extend_slice(&mut self, additional: &[u8]) -> Result<(), ()> {
        self.pop_terminator();

        self.buf.extend_from_slice(additional)
    }

    #[inline]
    fn inner_without_nil_terminator(&self) -> &[u8] {
        // Assert our invariant: `self.buf` must be null-terminated
        debug_assert!(self.buf.len() > 0);
        debug_assert_eq!(self.buf.last().copied(), Some(0));

        &self.buf[..self.buf.len() - 1]
    }

    /// Gets the underlying bytes written to this [`CString`] so far, without including the null terminator.
    ///
    /// # Example
    ///
    /// ```
    /// use heapless::CString;
    ///
    /// let mut cstr = CString::<5>::new();
    /// cstr.push_bytes(b"ab").unwrap();
    /// cstr.push_bytes(b"cd").unwrap();
    ///
    /// assert_eq!(
    ///     cstr.as_bytes_with_null(),
    ///     b"abcd\0"
    /// );
    /// ```
    #[inline]
    pub fn as_bytes_with_null(&self) -> &[u8] {
        &self.buf
    }

    /// Gets the underlying bytes written to this [`CString`] so far, without including the null terminator.
    ///
    /// # Example
    ///
    /// ```
    /// use heapless::CString;
    ///
    /// let mut cstr = CString::<5>::new();
    /// cstr.push_bytes(b"ab").unwrap();
    /// cstr.push_bytes(b"cd").unwrap();
    ///
    /// assert_eq!(
    ///     cstr.as_bytes(),
    ///     b"abcd"
    /// );
    /// ```
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        self.inner_without_nil_terminator()
    }

    ///
    pub fn as_ptr(&self) -> *const u8 {
        self.buf.as_ptr()
    }

    /// TODO
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.buf.as_mut_ptr()
    }
}

#[cfg(test)]
mod tests {
    use core::ffi::CStr;

    use super::CString;

    #[test]
    fn empty_cstring_is_valid() {
        let empty: CString<5> = CString::new();

        // &CStr's Default impl points to a slice that only contains a single element: the nul byte terminator
        assert_eq!(empty.as_cstr(), <&CStr>::default());
        assert_eq!(empty.as_bytes(), &[]);
        assert_eq!(empty.to_str(), Ok(""));
    }

    #[test]
    fn appends_bytes_correctly() {
        let mut cstr: CString<11> = CString::new();
        assert_eq!(cstr.to_str(), Ok(""));

        cstr.push_bytes(b"hello").unwrap();

        assert_eq!(cstr.to_str(), Ok("hello"));

        // Call must fail since `w\0rld` contains an interior nul byteassert_eq!(empty.to_str(), Ok("hello"));
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
    fn correctly_calculates_appended_length() {
        let mut cstr: CString<5> = CString::new();
        cstr.push_bytes(b"abcd").unwrap();
        assert_eq!(cstr.len(), 5);

        assert_eq!(
            cstr.size_if_appended_bytes(b"efgh"),
            // 4 bytes for "abcd", 4 bytes for "efgh" and a byte for the nul terminator
            Some(4 + "efgh".len() + 1)
        );

        assert_eq!(
            cstr.size_if_appended_bytes(b"efgh\0"),
            // 4 bytes for "abcd", 4 bytes for "efgh" and a byte for the nul terminator
            Some(4 + "efgh".len() + 1)
        );
    }
}
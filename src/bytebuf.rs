use core::{
    cmp,
    fmt,
    hash,
    iter,
    ops,
    slice,
};

use generic_array::ArrayLength;

use crate::vec::{IntoIter, Vec};

/// Wrapper around Vec<u8, N> to serialize and deserialize efficiently.
///
/// If [impl specialization] is stabilized, this type might be removed, and
/// the more efficient serde implemented on Vec<u8, N> directly.
///
/// [impl specialization]: https://github.com/rust-lang/rust/issues/31844/
pub struct ByteBuf<N>
where
    N: ArrayLength<u8>
{
    #[doc(hidden)]
    vec: crate::Vec::<u8, N>,
}

impl<N> ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    /// Constructs a new, empty `ByteBuf` with a fixed capacity of `N`
    #[inline]
    pub fn new() -> Self {
        ByteBuf { vec: Vec(crate::i::Vec::new()) }
    }

    /// Unwraps the Vec<u8, N>, same as `into_vec`.
    pub fn into_inner(self) -> Vec<u8, N> {
        self.vec
    }

    /// Unwraps the Vec<u8, N>, same as `into_inner`.
    pub fn into_vec(self) -> Vec<u8, N> {
        self.vec
    }

    /// Constructs a new byte buffer with a fixed capacity of `N` and fills it
    /// with the provided slice.
    ///
    /// This is equivalent to the following code:
    ///
    /// ```
    /// use heapless::ByteBuf;
    /// use heapless::consts::*;
    ///
    /// let mut bytes: ByteBuf<U16> = ByteBuf::new();
    /// bytes.extend_from_slice(&[1, 2, 3]);
    ///
    /// println!("hello, byte buffer! {}", &bytes);
    /// ```
    #[inline]
    pub fn from_slice(other: &[u8]) -> Result<Self, ()>
    {
        let mut new = ByteBuf::new();
        new.extend_from_slice(other)?;
        Ok(new)
    }

    /// APIs modeled after `std::io::Write` offer an interface of the form
    /// `write(&mut [u8]) -> Result<usize, E>`, with the contract that the
    /// Ok value signals how many bytes were written.
    ///
    /// This constructor allows wrapping such interfaces in a more ergonomic way,
    /// returning a byte buffer filled using the writer.
    pub fn from_writer<E>(
        write: impl FnOnce(&mut [u8]) -> core::result::Result<usize, E>
    )
        -> core::result::Result<Self, E>
    {
        let mut new = Self::new();
        new.resize_to_capacity();

        let result = write(&mut new);

        result.map(|count| {
            new.truncate(count);
            new
        })
    }

}

impl<N> Default for ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<N> Clone for ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    fn clone(&self) -> Self {
        Self { vec: self.vec.clone() }
    }
}

// The normal, boring implementation
// impl<N> fmt::Debug for ByteBuf<N>
// where
//     N: ArrayLength<u8>,
// {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         <[u8] as fmt::Debug>::fmt(self, f)
//     }
// }

// Somewhat nicer implementation
impl<N> fmt::Debug for ByteBuf<N>
where
    N: ArrayLength<u8>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO: There has to be a better way :'-)
        f.write_str("b\"")?;
        for ch in self.vec.iter().flat_map(|byte| core::ascii::escape_default(*byte)) {
            f.write_str(unsafe { core::str::from_utf8_unchecked(&[ch]) })?;
        }
        f.write_str("\"")?;
        Ok(())
    }
}

impl<N> fmt::Display for ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <[u8] as fmt::Debug>::fmt(self, f)
    }
}

impl<N> From<Vec<u8, N>> for ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    fn from(vec: Vec<u8, N>) -> Self {
        Self { vec }
    }
}

impl<'a, N> From<&'a [u8]> for ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    fn from(s: &'a [u8]) -> Self {
        let mut new = ByteBuf::new();
        new.extend_from_slice(s).unwrap();
        new
    }
}

impl<N> hash::Hash for ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    #[inline]
    fn hash<H: hash::Hasher>(&self, hasher: &mut H) {
        <Vec::<u8, N> as hash::Hash>::hash(&self.vec, hasher)
    }
}

impl<N> hash32::Hash for ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    #[inline]
    fn hash<H: hash32::Hasher>(&self, hasher: &mut H) {
        <Vec::<u8, N> as hash32::Hash>::hash(&self.vec, hasher)
    }
}

impl<N> ops::Deref for ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    type Target = Vec<u8, N>;

    fn deref(&self) -> &Self::Target {
        &self.vec
    }
}

impl<N> ops::DerefMut for ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.vec
    }
}

impl<N> Extend<u8> for ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = u8>,
    {
        self.vec.extend(iter)
    }
}

impl<'a, N> Extend<&'a u8> for ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = &'a u8>,
    {
        self.vec.extend(iter.into_iter().cloned())
    }
}

impl<'a, N> IntoIterator for &'a ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    type Item = &'a u8;
    type IntoIter = slice::Iter<'a, u8>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, N> IntoIterator for &'a mut ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    type Item = &'a mut u8;
    type IntoIter = slice::IterMut<'a, u8>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<N> iter::FromIterator<u8> for ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = u8>,
    {
        Self { vec: Vec::from_iter(iter) }
    }
}

impl<N> IntoIterator for ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    type Item = u8;
    type IntoIter = IntoIter<u8, N>;

    fn into_iter(self) -> Self::IntoIter {
        self.vec.into_iter()
    }
}

impl<N, Rhs> PartialEq<Rhs> for ByteBuf<N>
where
    N: ArrayLength<u8>,
    Rhs: ?Sized + AsRef<[u8]>,
{
    fn eq(&self, other: &Rhs) -> bool {
        // self.as_ref().eq(other.as_ref())
        let slice: &[u8] = self.as_ref();
        slice.eq(other.as_ref())
    }
}

impl<N, Rhs> PartialOrd<Rhs> for ByteBuf<N>
where
    N: ArrayLength<u8>,
    Rhs: ?Sized + AsRef<[u8]>,
{
    fn partial_cmp(&self, other: &Rhs) -> Option<cmp::Ordering> {
        // self.as_ref().partial_cmp(other.as_ref())
        let slice: &[u8] = self.as_ref();
        slice.partial_cmp(other.as_ref())
    }
}

impl<N> Eq for ByteBuf<N>
where
    N: ArrayLength<u8>
{
}

impl<N> fmt::Write for ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    fn write_str(&mut self, s: &str) -> Result<(), fmt::Error> {
        <Vec::<u8, N> as fmt::Write>::write_str(&mut self.vec, s)
    }
}

impl<N> AsRef<ByteBuf<N>> for ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    #[inline]
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<N> AsMut<ByteBuf<N>> for ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    #[inline]
    fn as_mut(&mut self) -> &mut Self {
        self
    }
}

impl<N> AsRef<Vec<u8, N>> for ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    #[inline]
    fn as_ref(&self) -> &Vec<u8, N> {
        &self.vec
    }
}

impl<N> AsMut<Vec<u8, N>> for ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    #[inline]
    fn as_mut(&mut self) -> &mut Vec<u8, N> {
        &mut self.vec
    }
}

impl<N> AsRef<[u8]> for ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self
    }
}

impl<N> AsMut<[u8]> for ByteBuf<N>
where
    N: ArrayLength<u8>,
{
    #[inline]
    fn as_mut(&mut self) -> &mut [u8] {
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn slice_insertion() {
        let mut v = ByteBuf::<crate::consts::U8>::from_slice(&[1, 2, 6, 7, 8]).unwrap();
        v.insert_slice_at(&[3, 4, 5], 2).unwrap();
        assert_eq!(v, &[1, 2, 3, 4, 5, 6, 7, 8]);
        let x = v.remove(0).unwrap();
        assert_eq!(x, 1);
        let x = v.remove(2).unwrap();
        assert_eq!(x, 4);
        assert!(v.remove(6).is_err());
        assert!(v.remove(5).is_ok());
    }

    #[test]
    fn to_byte_buf() {
        let v = ByteBuf::<crate::consts::U8>::from_slice(&[1, 2, 6, 7, 8]).unwrap();
        let w: ByteBuf<crate::consts::U9> = v.to_byte_buf();
        assert_eq!(v, w);
        let w: ByteBuf<crate::consts::U5> = v.try_to_byte_buf().unwrap();
        assert_eq!(v, w);
    }

    #[test]
    fn debug() {
        let bytes = ByteBuf::<crate::consts::U24>::from_slice(b"\xa2ebytesC\x01\x02\x03hbyte_bufC\x01\x02\x03");
        println!("{:?}", bytes);
    }
}

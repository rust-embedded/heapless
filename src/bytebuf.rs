use core::{
    cmp,
    fmt,
    hash,
    iter,
    ops,
    slice,
};

use generic_array::{
    ArrayLength,
    typenum::{IsGreaterOrEqual, True},
};

use crate::vec::{IntoIter, Vec};

/// Wrapper around Vec<u8, N> to serialize and deserialize efficiently.
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

    /// Embed in bigger vector.
    // We can't implement TryInto since it would clash with blanket implementations.
    pub fn embed<M>(&self) -> ByteBuf<M>
    where
        M: ArrayLength<u8> + IsGreaterOrEqual<N, Output = True>,
    {
        match ByteBuf::from_slice(self) {
            Ok(vec) => vec,
            _ => unreachable!(),
        }
    }

    /// Fallible embed.
    pub fn try_embed<M>(&self) -> Result<ByteBuf<M>, ()>
    where
        M: ArrayLength<u8>,
    {
        ByteBuf::from_slice(self)
    }

    // cf. https://internals.rust-lang.org/t/add-vec-insert-slice-at-to-insert-the-content-of-a-slice-at-an-arbitrary-index/11008/3
    /// Insert byte slice at given index, if capacity allows it.
    pub fn insert_slice_at(&mut self, slice: &[u8], at: usize) -> core::result::Result<(), ()> {
        let l = slice.len();
        let before = self.len();

        // make space
        self.resize_default(before + l)?;

        // move back existing
        let raw: &mut [u8] = &mut self.vec;
        raw.copy_within(at..before, at + l);

        // insert slice
        raw[at..][..l].copy_from_slice(slice);

        Ok(())
    }

    /// Unwraps the Vec<u8, N>.
    pub fn into_inner(self) -> Vec<u8, N> {
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
    /// bytes.extend_from_slice(&[1, 2, 3]).unwrap();
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

    /// APIs modeled after `std::io::Read` offer an interface of the form
    /// `f(&mut [u8]) -> Result<usize, E>`, with the contract that the
    /// Ok-value signals how many bytes were written.
    ///
    /// This constructor allows wrapping such interfaces in a more ergonomic way,
    /// returning a byte buffer filled using `f`.
    pub fn try_read<E>(
        f: impl FnOnce(&mut [u8]) -> core::result::Result<usize, E>
    )
        -> core::result::Result<Self, E>
    {
        let mut data = Self::new();
        data.resize_to_capacity();

        let result = f(&mut data);

        result.map(|count| {
            data.truncate(count);
            data
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
        use core::ascii::escape_default;
        f.write_str("b'")?;
        for byte in &self.vec {
            for ch in escape_default(*byte) {
                f.write_str(unsafe { core::str::from_utf8_unchecked(&[ch]) })?;
            }
        }
        f.write_str("'")?;
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

// impl<N1, N2> PartialEq<ByteBuf<N2>> for ByteBuf<N1>
// where
//     N1: ArrayLength<u8>,
//     N2: ArrayLength<u8>,
// {
//     fn eq(&self, other: &ByteBuf<N2>) -> bool {
//         <[u8]>::eq(&self.vec, &***other)
//     }
// }

// macro_rules! eq {
//     ($Lhs:ty, $Rhs:ty) => {
//         impl<'a, 'b, N> PartialEq<$Rhs> for $Lhs
//         where
//             N: ArrayLength<u8>,
//         {
//             fn eq(&self, other: &$Rhs) -> bool {
//                 <[u8]>::eq(self, &other[..])
//             }
//         }
//     };
// }

// eq!(ByteBuf<N>, [u8]);
// eq!(ByteBuf<N>, &'a [u8]);
// eq!(ByteBuf<N>, &'a mut [u8]);

// macro_rules! array {
//     ($($N:expr),+) => {
//         $(
//             eq!(ByteBuf<N>, [u8; $N]);
//             eq!(ByteBuf<N>, &'a [u8; $N]);
//         )+
//     }
// }

// array!(
//     0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
//     26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
//     49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64
// );

// impl<N> Ord for ByteBuf<N>
// where
//     N: ArrayLength<u8>,
// {
//     fn cmp(...)
// }

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
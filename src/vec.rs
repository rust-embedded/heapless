use core::{fmt, hash, iter::FromIterator, mem::MaybeUninit, ops, ptr, slice};
use hash32;

use crate::sealed::spsc::Uxx;

/// A fixed capacity [`Vec`](https://doc.rust-lang.org/std/vec/struct.Vec.html)
///
/// # Examples
///
/// ```
/// use heapless::Vec;
///
///
/// // A vector with a fixed capacity of 8 elements allocated on the stack
/// let mut vec = Vec::<_, 8>::new();
/// vec.push(1);
/// vec.push(2);
///
/// assert_eq!(vec.len(), 2);
/// assert_eq!(vec[0], 1);
///
/// assert_eq!(vec.pop(), Some(2));
/// assert_eq!(vec.len(), 1);
///
/// vec[0] = 7;
/// assert_eq!(vec[0], 7);
///
/// vec.extend([1, 2, 3].iter().cloned());
///
/// for x in &vec {
///     println!("{}", x);
/// }
/// assert_eq!(*vec, [7, 1, 2, 3]);
/// ```
///
/// The length type of `Vec` and `Vec`-based containers is generic and can use `u8`, `u16`, or
/// `usize`. Using smaller length types can reduce memory footprint for containers with low
/// alignment requirements.  The easiest way to construct a `Vec` with a smaller index type is to
/// use the [`u8`] and [`u16`] constructors.
///
/// [`u8`]: struct.Vec.html#method.u8
/// [`u16`]: struct.Vec.html#method.u16
///
/// *IMPORTANT*: `Vec<_, u8, N>` has a maximum capacity of 255 elements; `Vec<_,
/// u16, N>` has a maximum capacity of 65535 elements.
pub struct VecBase<T, U: Uxx, const N: usize> {
    buffer: MaybeUninit<[T; N]>,
    len: U,
}

pub type Vec<T, const N: usize> = VecBase<T, usize, N>;

macro_rules! impl_new {
    ($Uxx:ident, $name:ident) => {
        impl<T, const N: usize> VecBase<T, $Uxx, N> {
            /// Constructs a new, empty vector with a fixed capacity of `N`
            /// `Vec` `const` constructor; wrap the returned value in [`Vec`](../struct.Vec.html)
            pub const fn $name() -> Self {
                Self {
                    buffer: MaybeUninit::uninit(),
                    len: 0,
                }
            }

            /// Returns the maximum number of elements the vector can hold.
            pub const fn capacity(&self) -> usize {
                N
            }
        }
    };
}

impl_new!(u8, u8);
impl_new!(u16, u16);
impl_new!(usize, usize);

impl<T, const N: usize> Vec<T, N> {
    /// Constructs a new, empty vector with a fixed capacity of `N` and length type of `usize`
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::Vec;
    ///
    /// // allocate the vector on the stack
    /// let mut x: Vec<u8, _, 16> = Vec::new();
    ///
    /// // allocate the vector in a static variable
    /// static mut X: Vec<u8, usize, 16> = Vec::new();
    /// ```
    /// `Vec` `const` constructor; wrap the returned value in [`Vec`](../struct.Vec.html)
    pub const fn new() -> Self {
        Self::usize()
    }
}

impl<T, U: Uxx, const N: usize> VecBase<T, U, N> {
    pub(crate) fn capacity_nonconst(&self) -> usize {
        N
    }

    /// Constructs a new vector with a fixed capacity of `N` and fills it
    /// with the provided slice.
    ///
    /// This is equivalent to the following code:
    ///
    /// ```
    /// use heapless::Vec;
    ///
    /// let mut v: Vec<u8, 16> = Vec::new();
    /// v.extend_from_slice(&[1, 2, 3]).unwrap();
    /// ```
    #[inline]
    pub fn from_slice(other: &[T]) -> Result<Self, ()>
    where
        T: Clone,
    {
        let mut v = VecBase::default();
        v.extend_from_slice(other)?;
        Ok(v)
    }

    /// Clones a vec into a new vec
    pub(crate) fn clone(&self) -> Self
    where
        T: Clone,
    {
        let mut new = Self::default();
        new.extend_from_slice(self.as_slice()).unwrap();
        new
    }

    /// Extracts a slice containing the entire vector.
    ///
    /// Equivalent to `&s[..]`.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::Vec;
    /// let buffer: Vec<u8, 5> = Vec::from_slice(&[1, 2, 3, 5, 8]).unwrap();
    /// assert_eq!(buffer.as_slice(), &[1, 2, 3, 5, 8]);
    /// ```
    pub fn as_slice(&self) -> &[T] {
        // NOTE(unsafe) avoid bound checks in the slicing operation
        // &buffer[..self.len]
        unsafe { slice::from_raw_parts(self.buffer.as_ptr() as *const T, self.len.into()) }
    }

    /// Extracts a mutable slice containing the entire vector.
    ///
    /// Equivalent to `&s[..]`.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::Vec;
    /// let mut buffer: Vec<u8, 5> = Vec::from_slice(&[1, 2, 3, 5, 8]).unwrap();
    /// buffer[0] = 9;
    /// assert_eq!(buffer.as_slice(), &[9, 2, 3, 5, 8]);
    /// ```
    pub(crate) fn as_mut_slice(&mut self) -> &mut [T] {
        // NOTE(unsafe) avoid bound checks in the slicing operation
        // &mut buffer[..self.len]
        unsafe { slice::from_raw_parts_mut(self.buffer.as_mut_ptr() as *mut T, self.len.into()) }
    }

    /// Clears the vector, removing all values.
    // PER: Check if non drop types correctly optimized.
    pub fn clear(&mut self) {
        self.truncate(0);
    }

    /// Extends the vec from an iterator.
    ///
    /// # Panic
    ///
    /// Panics if the vec cannot hold all elements of the iterator.
    pub fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        for elem in iter {
            self.push(elem).ok().unwrap()
        }
    }

    /// Clones and appends all elements in a slice to the `Vec`.
    ///
    /// Iterates over the slice `other`, clones each element, and then appends
    /// it to this `Vec`. The `other` vector is traversed in-order.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::Vec;
    ///
    /// let mut vec = Vec::<u8, 8>::new();
    /// vec.push(1).unwrap();
    /// vec.extend_from_slice(&[2, 3, 4]).unwrap();
    /// assert_eq!(*vec, [1, 2, 3, 4]);
    /// ```
    pub fn extend_from_slice(&mut self, other: &[T]) -> Result<(), ()>
    where
        T: Clone,
    {
        if self.len.into() + other.len() > self.capacity_nonconst() {
            // won't fit in the `Vec`; don't modify anything and return an error
            Err(())
        } else {
            for elem in other {
                unsafe {
                    self.push_unchecked(elem.clone());
                }
            }
            Ok(())
        }
    }

    /// Removes the last element from a vector and returns it, or `None` if it's empty
    pub fn pop(&mut self) -> Option<T> {
        if self.len.into() != 0 {
            Some(unsafe { self.pop_unchecked() })
        } else {
            None
        }
    }

    /// Appends an `item` to the back of the collection
    ///
    /// Returns back the `item` if the vector is full
    pub fn push(&mut self, item: T) -> Result<(), T> {
        if self.len.into() < self.capacity_nonconst() {
            unsafe { self.push_unchecked(item) }
            Ok(())
        } else {
            Err(item)
        }
    }

    /// Removes the last element from a vector and returns it
    ///
    /// # Safety
    ///
    /// This assumes the vec to have at least one element.
    pub(crate) unsafe fn pop_unchecked(&mut self) -> T {
        debug_assert!(!self.as_slice().is_empty());

        self.len -= U::truncate(1);
        (self.buffer.as_ptr() as *const T)
            .add(self.len.into())
            .read()
    }

    /// Appends an `item` to the back of the collection
    ///
    /// # Safety
    ///
    /// This assumes the vec is not full.
    pub unsafe fn push_unchecked(&mut self, item: T) {
        // NOTE(ptr::write) the memory slot that we are about to write to is uninitialized. We
        // use `ptr::write` to avoid running `T`'s destructor on the uninitialized memory
        debug_assert!(!self.is_full());
        (self.buffer.as_mut_ptr() as *mut T)
            .add(self.len.into())
            .write(item);

        self.len += U::truncate(1);
    }

    /// Shortens the vector, keeping the first `len` elements and dropping the rest.
    // PER: Check that non drop types are correctly optimized
    pub fn truncate(&mut self, len: usize) {
        unsafe {
            // drop any extra elements
            while len < self.len.into() {
                // decrement len before the drop_in_place(), so a panic on Drop
                // doesn't re-drop the just-failed value.
                self.len -= U::truncate(1);
                let len = self.len;
                ptr::drop_in_place(self.as_mut_slice().get_unchecked_mut(len.into()));
            }
        }
    }

    /// Resizes the Vec in-place so that len is equal to new_len.
    ///
    /// If new_len is greater than len, the Vec is extended by the
    /// difference, with each additional slot filled with value. If
    /// new_len is less than len, the Vec is simply truncated.
    ///
    /// See also [`resize_default`](struct.Vec.html#method.resize_default).
    pub fn resize(&mut self, new_len: usize, value: T) -> Result<(), ()>
    where
        T: Clone,
    {
        if new_len > self.capacity_nonconst() {
            return Err(());
        }

        if new_len > self.len.into() {
            while self.len.into() < new_len {
                self.push(value.clone()).ok();
            }
        } else {
            self.truncate(new_len);
        }

        Ok(())
    }

    /// Resizes the `Vec` in-place so that `len` is equal to `new_len`.
    ///
    /// If `new_len` is greater than `len`, the `Vec` is extended by the
    /// difference, with each additional slot filled with `U::truncate(0)`.
    /// If `new_len` is less than `len`, the `Vec` is simply truncated.
    ///
    /// See also [`resize`](struct.Vec.html#method.resize).
    pub fn resize_default(&mut self, new_len: usize) -> Result<(), ()>
    where
        T: Clone + Default,
    {
        self.resize(new_len, T::default())
    }

    /// Forces the length of the vector to `new_len`.
    ///
    /// This is a low-level operation that maintains none of the normal
    /// invariants of the type. Normally changing the length of a vector
    /// is done using one of the safe operations instead, such as
    /// [`truncate`], [`resize`], [`extend`], or [`clear`].
    ///
    /// [`truncate`]: #method.truncate
    /// [`resize`]: #method.resize
    /// [`extend`]: https://doc.rust-lang.org/stable/core/iter/trait.Extend.html#tymethod.extend
    /// [`clear`]: #method.clear
    ///
    /// # Safety
    ///
    /// - `new_len` must be less than or equal to [`capacity()`].
    /// - The elements at `old_len..new_len` must be initialized.
    ///
    /// [`capacity()`]: #method.capacity
    ///
    /// # Examples
    ///
    /// This method can be useful for situations in which the vector
    /// is serving as a buffer for other code, particularly over FFI:
    ///
    /// ```no_run
    /// # #![allow(dead_code)]
    /// use heapless::Vec;
    ///
    /// # // This is just a minimal skeleton for the doc example;
    /// # // don't use this as a starting point for a real library.
    /// # pub struct StreamWrapper { strm: *mut core::ffi::c_void }
    /// # const Z_OK: i32 = 0;
    /// # extern "C" {
    /// #     fn deflateGetDictionary(
    /// #         strm: *mut core::ffi::c_void,
    /// #         dictionary: *mut u8,
    /// #         dictLength: *mut usize,
    /// #     ) -> i32;
    /// # }
    /// # impl StreamWrapper {
    /// pub fn get_dictionary(&self) -> Option<Vec<u8, 32768>> {
    ///     // Per the FFI method's docs, "32768 bytes is always enough".
    ///     let mut dict = Vec::new();
    ///     let mut dict_length = 0;
    ///     // SAFETY: When `deflateGetDictionary` returns `Z_OK`, it holds that:
    ///     // 1. `dict_length` elements were initialized.
    ///     // 2. `dict_length` <= the capacity (32_768)
    ///     // which makes `set_len` safe to call.
    ///     unsafe {
    ///         // Make the FFI call...
    ///         let r = deflateGetDictionary(self.strm, dict.as_mut_ptr(), &mut dict_length);
    ///         if r == Z_OK {
    ///             // ...and update the length to what was initialized.
    ///             dict.set_len(dict_length);
    ///             Some(dict)
    ///         } else {
    ///             None
    ///         }
    ///     }
    /// }
    /// # }
    /// ```
    ///
    /// While the following example is sound, there is a memory leak since
    /// the inner vectors were not freed prior to the `set_len` call:
    ///
    /// ```
    /// use core::iter::FromIterator;
    /// use heapless::Vec;
    ///
    /// let mut vec = Vec::<Vec<u8, 3>, 3>::from_iter(
    ///     [
    ///         Vec::from_iter([1, 0, 0].iter().cloned()),
    ///         Vec::from_iter([0, 1, 0].iter().cloned()),
    ///         Vec::from_iter([0, 0, 1].iter().cloned()),
    ///     ]
    ///     .iter()
    ///     .cloned()
    /// );
    /// // SAFETY:
    /// // 1. `old_len..0` is empty so no elements need to be initialized.
    /// // 2. `0 <= capacity` always holds whatever `capacity` is.
    /// unsafe {
    ///     vec.set_len(0);
    /// }
    /// ```
    ///
    /// Normally, here, one would use [`clear`] instead to correctly drop
    /// the contents and thus not leak memory.
    pub unsafe fn set_len(&mut self, new_len: usize) {
        debug_assert!(new_len <= self.capacity_nonconst());

        self.len = U::truncate(new_len)
    }

    /// Removes an element from the vector and returns it.
    ///
    /// The removed element is replaced by the last element of the vector.
    ///
    /// This does not preserve ordering, but is O(1).
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::Vec;
    ///// use heapless::consts::*;
    ///
    /// let mut v: Vec<_, 8> = Vec::new();
    /// v.push("foo").unwrap();
    /// v.push("bar").unwrap();
    /// v.push("baz").unwrap();
    /// v.push("qux").unwrap();
    ///
    /// assert_eq!(v.swap_remove(1), "bar");
    /// assert_eq!(&*v, ["foo", "qux", "baz"]);
    ///
    /// assert_eq!(v.swap_remove(0), "foo");
    /// assert_eq!(&*v, ["baz", "qux"]);
    /// ```
    pub fn swap_remove(&mut self, index: usize) -> T {
        assert!(index < self.len.into());
        unsafe { self.swap_remove_unchecked(index) }
    }

    /// Removes an element from the vector and returns it.
    ///
    /// The removed element is replaced by the last element of the vector.
    ///
    /// This does not preserve ordering, but is O(1).
    ///
    /// # Safety
    ///
    ///  Assumes `index` within bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::Vec;
    ///
    /// let mut v: Vec<_, 8> = Vec::new();
    /// v.push("foo").unwrap();
    /// v.push("bar").unwrap();
    /// v.push("baz").unwrap();
    /// v.push("qux").unwrap();
    ///
    /// assert_eq!(unsafe { v.swap_remove_unchecked(1) }, "bar");
    /// assert_eq!(&*v, ["foo", "qux", "baz"]);
    ///
    /// assert_eq!(unsafe { v.swap_remove_unchecked(0) }, "foo");
    /// assert_eq!(&*v, ["baz", "qux"]);
    /// ```
    pub unsafe fn swap_remove_unchecked(&mut self, index: usize) -> T {
        let length = self.len();
        debug_assert!(index < length);
        ptr::swap(
            self.as_mut_slice().get_unchecked_mut(index),
            self.as_mut_slice().get_unchecked_mut(length - 1),
        );
        self.pop_unchecked()
    }

    /// Returns true if the vec is full
    #[inline]
    pub fn is_full(&self) -> bool {
        self.len.into() == self.capacity_nonconst()
    }

    /// Returns `true` if `needle` is a prefix of the Vec.
    ///
    /// Always returns `true` if `needle` is an empty slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::Vec;
    ///
    /// let v: Vec<_, 8> = Vec::from_slice(b"abc").unwrap();
    /// assert_eq!(v.starts_with(b""), true);
    /// assert_eq!(v.starts_with(b"ab"), true);
    /// assert_eq!(v.starts_with(b"bc"), false);
    /// ```
    #[inline]
    pub fn starts_with(&self, needle: &[T]) -> bool
    where
        T: PartialEq,
    {
        let n = needle.len();
        self.len.into() >= n && needle == &self[..n]
    }

    /// Returns `true` if `needle` is a suffix of the Vec.
    ///
    /// Always returns `true` if `needle` is an empty slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::Vec;
    ///
    /// let v: Vec<_, 8> = Vec::from_slice(b"abc").unwrap();
    /// assert_eq!(v.ends_with(b""), true);
    /// assert_eq!(v.ends_with(b"ab"), false);
    /// assert_eq!(v.ends_with(b"bc"), true);
    /// ```
    #[inline]
    pub fn ends_with(&self, needle: &[T]) -> bool
    where
        T: PartialEq,
    {
        let (v, n) = (self.len(), needle.len());
        v >= n && needle == &self[v - n..]
    }
}

// Trait implementations

impl<T, U: Uxx, const N: usize> Default for VecBase<T, U, N> {
    fn default() -> Self {
        Self {
            buffer: MaybeUninit::uninit(),
            len: U::truncate(0),
        }
    }
}

impl<T, U: Uxx, const N: usize> fmt::Debug for VecBase<T, U, N>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <[T] as fmt::Debug>::fmt(self, f)
    }
}

impl<U: Uxx, const N: usize> fmt::Write for VecBase<u8, U, N> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        match self.extend_from_slice(s.as_bytes()) {
            Ok(()) => Ok(()),
            Err(_) => Err(fmt::Error),
        }
    }
}

// PER: Please check if non drop types are correctly optimized
impl<T, U: Uxx, const N: usize> Drop for VecBase<T, U, N> {
    fn drop(&mut self) {
        // We drop each element used in the vector by turning into a &mut[T]
        unsafe {
            ptr::drop_in_place(self.as_mut_slice());
        }
    }
}

impl<T, U: Uxx, const N: usize> Extend<T> for VecBase<T, U, N> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        self.extend(iter)
    }
}

impl<'a, T, U: Uxx, const N: usize> Extend<&'a T> for VecBase<T, U, N>
where
    T: 'a + Copy,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = &'a T>,
    {
        self.extend(iter.into_iter().cloned())
    }
}

impl<T, U: Uxx, const N: usize> hash::Hash for VecBase<T, U, N>
where
    T: core::hash::Hash,
{
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        <[T] as hash::Hash>::hash(self, state)
    }
}

impl<T, U: Uxx, const N: usize> hash32::Hash for VecBase<T, U, N>
where
    T: hash32::Hash,
{
    fn hash<H: hash32::Hasher>(&self, state: &mut H) {
        <[T] as hash32::Hash>::hash(self, state)
    }
}

impl<'a, T, U: Uxx, const N: usize> IntoIterator for &'a VecBase<T, U, N> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T, U: Uxx, const N: usize> IntoIterator for &'a mut VecBase<T, U, N> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T, U: Uxx, const N: usize> FromIterator<T> for VecBase<T, U, N> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let mut vec = VecBase::default();
        for i in iter {
            vec.push(i).ok().expect("Vec::from_iter overflow");
        }
        vec
    }
}

/// An iterator that moves out of an [`Vec`][`Vec`].
///
/// This struct is created by calling the `into_iter` method on [`Vec`][`Vec`].
///
/// [`Vec`]: (https://doc.rust-lang.org/std/vec/struct.Vec.html)
///
pub struct IntoIter<T, U: Uxx, const N: usize> {
    vec: VecBase<T, U, N>,
    next: usize,
}

impl<T, U: Uxx, const N: usize> Iterator for IntoIter<T, U, N> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        if self.next < self.vec.len() {
            let item = unsafe { (self.vec.buffer.as_ptr() as *const T).add(self.next).read() };
            self.next += 1;
            Some(item)
        } else {
            None
        }
    }
}

impl<T, U: Uxx, const N: usize> Clone for IntoIter<T, U, N>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        let mut vec = VecBase::default();

        if self.next < self.vec.len() {
            let s = unsafe {
                slice::from_raw_parts(
                    (self.vec.buffer.as_ptr() as *const T).add(self.next),
                    self.vec.len() - self.next,
                )
            };
            vec.extend_from_slice(s).ok();
        }

        Self { vec, next: 0 }
    }
}

// PER: is this correct
impl<T, U: Uxx, const N: usize> Drop for IntoIter<T, U, N> {
    fn drop(&mut self) {
        unsafe {
            // Drop all the elements that have not been moved out of vec
            ptr::drop_in_place(&mut self.vec.as_mut_slice()[self.next..]);
            // Prevent dropping of other elements
            self.vec.len = U::truncate(0);
        }
    }
}

impl<T, U: Uxx, const N: usize> IntoIterator for VecBase<T, U, N> {
    type Item = T;
    type IntoIter = IntoIter<T, U, N>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter { vec: self, next: 0 }
    }
}

impl<A, B, U1: Uxx, U2: Uxx, const N1: usize, const N2: usize> PartialEq<VecBase<B, U2, N2>>
    for VecBase<A, U1, N1>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &VecBase<B, U2, N2>) -> bool {
        <[A]>::eq(self, &**other)
    }
}

// Vec<A, U, N> == [B]
impl<A, B, U: Uxx, const N: usize> PartialEq<[B]> for VecBase<A, U, N>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &[B]) -> bool {
        <[A]>::eq(self, &other[..])
    }
}

// Vec<A, U, N> == &[B]
impl<A, B, U: Uxx, const N: usize> PartialEq<&[B]> for VecBase<A, U, N>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &&[B]) -> bool {
        <[A]>::eq(self, &other[..])
    }
}

// Vec<A, U, N> == &mut [B]
impl<A, B, U: Uxx, const N: usize> PartialEq<&mut [B]> for VecBase<A, U, N>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &&mut [B]) -> bool {
        <[A]>::eq(self, &other[..])
    }
}

// Vec<A, U, N> == [B; M]
// Equality does not require equal capacity
impl<A, B, U: Uxx, const N: usize, const M: usize> PartialEq<[B; M]> for VecBase<A, U, N>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &[B; M]) -> bool {
        <[A]>::eq(self, &other[..])
    }
}

// Vec<A, U, N> == &[B; M]
// Equality does not require equal capacity
impl<A, B, U: Uxx, const N: usize, const M: usize> PartialEq<&[B; M]> for VecBase<A, U, N>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &&[B; M]) -> bool {
        <[A]>::eq(self, &other[..])
    }
}

// Implements Eq if underlying data is Eq
impl<T, U: Uxx, const N: usize> Eq for VecBase<T, U, N> where T: Eq {}

impl<T, U: Uxx, const N: usize> ops::Deref for VecBase<T, U, N> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, U: Uxx, const N: usize> ops::DerefMut for VecBase<T, U, N> {
    fn deref_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T, U: Uxx, const N: usize> AsRef<VecBase<T, U, N>> for VecBase<T, U, N> {
    #[inline]
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<T, U: Uxx, const N: usize> AsMut<VecBase<T, U, N>> for VecBase<T, U, N> {
    #[inline]
    fn as_mut(&mut self) -> &mut Self {
        self
    }
}

impl<T, U: Uxx, const N: usize> AsRef<[T]> for VecBase<T, U, N> {
    #[inline]
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T, U: Uxx, const N: usize> AsMut<[T]> for VecBase<T, U, N> {
    #[inline]
    fn as_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<T, U: Uxx, const N: usize> Clone for VecBase<T, U, N>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        self.clone()
    }
}

#[cfg(test)]
mod tests {
    use crate::Vec;
    use core::fmt::Write;

    #[test]
    fn static_new() {
        static mut _V: Vec<i32, 4> = Vec::new();
    }

    #[test]
    fn stack_new() {
        static mut _V: Vec<i32, 4> = Vec::new();
    }

    macro_rules! droppable {
        () => {
            struct Droppable;
            impl Droppable {
                fn new() -> Self {
                    unsafe {
                        COUNT += 1;
                    }
                    Droppable
                }
            }
            impl Drop for Droppable {
                fn drop(&mut self) {
                    unsafe {
                        COUNT -= 1;
                    }
                }
            }

            static mut COUNT: i32 = 0;
        };
    }

    #[test]
    fn drop() {
        droppable!();

        {
            let mut v: Vec<Droppable, 2> = Vec::new();
            v.push(Droppable::new()).ok().unwrap();
            v.push(Droppable::new()).ok().unwrap();
            v.pop().unwrap();
        }

        assert_eq!(unsafe { COUNT }, 0);

        {
            let mut v: Vec<Droppable, 2> = Vec::new();
            v.push(Droppable::new()).ok().unwrap();
            v.push(Droppable::new()).ok().unwrap();
        }

        assert_eq!(unsafe { COUNT }, 0);
    }

    #[test]
    fn eq() {
        let mut xs: Vec<i32, 4> = Vec::new();
        let mut ys: Vec<i32, 8> = Vec::new();

        assert_eq!(xs, ys);

        xs.push(1).unwrap();
        ys.push(1).unwrap();

        assert_eq!(xs, ys);
    }

    #[test]
    fn full() {
        let mut v: Vec<i32, 4> = Vec::new();

        v.push(0).unwrap();
        v.push(1).unwrap();
        v.push(2).unwrap();
        v.push(3).unwrap();

        assert!(v.push(4).is_err());
    }

    #[test]
    fn iter() {
        let mut v: Vec<i32, 4> = Vec::new();

        v.push(0).unwrap();
        v.push(1).unwrap();
        v.push(2).unwrap();
        v.push(3).unwrap();

        let mut items = v.iter();

        assert_eq!(items.next(), Some(&0));
        assert_eq!(items.next(), Some(&1));
        assert_eq!(items.next(), Some(&2));
        assert_eq!(items.next(), Some(&3));
        assert_eq!(items.next(), None);
    }

    #[test]
    fn iter_mut() {
        let mut v: Vec<i32, 4> = Vec::new();

        v.push(0).unwrap();
        v.push(1).unwrap();
        v.push(2).unwrap();
        v.push(3).unwrap();

        let mut items = v.iter_mut();

        assert_eq!(items.next(), Some(&mut 0));
        assert_eq!(items.next(), Some(&mut 1));
        assert_eq!(items.next(), Some(&mut 2));
        assert_eq!(items.next(), Some(&mut 3));
        assert_eq!(items.next(), None);
    }

    #[test]
    fn collect_from_iter() {
        let slice = &[1, 2, 3];
        let vec: Vec<i32, 4> = slice.iter().cloned().collect();
        // PER: Auto deref did not work
        assert_eq!(vec.as_slice(), slice);
    }

    #[test]
    #[should_panic]
    fn collect_from_iter_overfull() {
        let slice = &[1, 2, 3];
        let _vec = slice.iter().cloned().collect::<Vec<_, 2>>();
    }

    #[test]
    fn iter_move() {
        let mut v: Vec<i32, 4> = Vec::new();
        v.push(0).unwrap();
        v.push(1).unwrap();
        v.push(2).unwrap();
        v.push(3).unwrap();

        let mut items = v.into_iter();

        assert_eq!(items.next(), Some(0));
        assert_eq!(items.next(), Some(1));
        assert_eq!(items.next(), Some(2));
        assert_eq!(items.next(), Some(3));
        assert_eq!(items.next(), None);
    }

    #[test]
    fn iter_move_drop() {
        droppable!();

        {
            let mut vec: Vec<Droppable, 2> = Vec::new();
            vec.push(Droppable::new()).ok().unwrap();
            vec.push(Droppable::new()).ok().unwrap();
            let mut items = vec.into_iter();
            // Move all
            let _ = items.next();
            let _ = items.next();
        }

        assert_eq!(unsafe { COUNT }, 0);

        {
            let mut vec: Vec<Droppable, 2> = Vec::new();
            vec.push(Droppable::new()).ok().unwrap();
            vec.push(Droppable::new()).ok().unwrap();
            let _items = vec.into_iter();
            // Move none
        }

        assert_eq!(unsafe { COUNT }, 0);

        {
            let mut vec: Vec<Droppable, 2> = Vec::new();
            vec.push(Droppable::new()).ok().unwrap();
            vec.push(Droppable::new()).ok().unwrap();
            let mut items = vec.into_iter();
            let _ = items.next(); // Move partly
        }

        assert_eq!(unsafe { COUNT }, 0);
    }

    #[test]
    fn push_and_pop() {
        let mut v: Vec<i32, 4> = Vec::new();
        assert_eq!(v.len(), 0);

        assert_eq!(v.pop(), None);
        assert_eq!(v.len(), 0);

        v.push(0).unwrap();
        assert_eq!(v.len(), 1);

        assert_eq!(v.pop(), Some(0));
        assert_eq!(v.len(), 0);

        assert_eq!(v.pop(), None);
        assert_eq!(v.len(), 0);
    }

    #[test]
    fn resize_size_limit() {
        let mut v: Vec<u8, 4> = Vec::new();

        v.resize(0, 0).unwrap();
        v.resize(4, 0).unwrap();
        v.resize(5, 0).err().expect("full");
    }

    #[test]
    fn resize_length_cases() {
        let mut v: Vec<u8, 4> = Vec::new();

        assert_eq!(v.len(), 0);

        // Grow by 1
        v.resize(1, 0).unwrap();
        assert_eq!(v.len(), 1);

        // Grow by 2
        v.resize(3, 0).unwrap();
        assert_eq!(v.len(), 3);

        // Resize to current size
        v.resize(3, 0).unwrap();
        assert_eq!(v.len(), 3);

        // Shrink by 1
        v.resize(2, 0).unwrap();
        assert_eq!(v.len(), 2);

        // Shrink by 2
        v.resize(0, 0).unwrap();
        assert_eq!(v.len(), 0);
    }

    #[test]
    fn resize_contents() {
        let mut v: Vec<u8, 4> = Vec::new();

        // New entries take supplied value when growing
        v.resize(1, 17).unwrap();
        assert_eq!(v[0], 17);

        // Old values aren't changed when growing
        v.resize(2, 18).unwrap();
        assert_eq!(v[0], 17);
        assert_eq!(v[1], 18);

        // Old values aren't changed when length unchanged
        v.resize(2, 0).unwrap();
        assert_eq!(v[0], 17);
        assert_eq!(v[1], 18);

        // Old values aren't changed when shrinking
        v.resize(1, 0).unwrap();
        assert_eq!(v[0], 17);
    }

    #[test]
    fn resize_default() {
        let mut v: Vec<u8, 4> = Vec::new();

        // resize_default is implemented using resize, so just check the
        // correct value is being written.
        v.resize_default(1).unwrap();
        assert_eq!(v[0], 0);
    }

    #[test]
    fn write() {
        let mut v: Vec<u8, 4> = Vec::new();
        write!(v, "{:x}", 1234).unwrap();
        assert_eq!(&v[..], b"4d2");
    }

    #[test]
    fn extend_from_slice() {
        let mut v: Vec<u8, 4> = Vec::new();
        assert_eq!(v.len(), 0);
        v.extend_from_slice(&[1, 2]).unwrap();
        assert_eq!(v.len(), 2);
        assert_eq!(v.as_slice(), &[1, 2]);
        v.extend_from_slice(&[3]).unwrap();
        assert_eq!(v.len(), 3);
        assert_eq!(v.as_slice(), &[1, 2, 3]);
        assert!(v.extend_from_slice(&[4, 5]).is_err());
        assert_eq!(v.len(), 3);
        assert_eq!(v.as_slice(), &[1, 2, 3]);
    }

    #[test]
    fn from_slice() {
        // Successful construction
        let v: Vec<u8, 4> = Vec::from_slice(&[1, 2, 3]).unwrap();
        assert_eq!(v.len(), 3);
        assert_eq!(v.as_slice(), &[1, 2, 3]);

        // Slice too large
        assert!(Vec::<u8, 2>::from_slice(&[1, 2, 3]).is_err());
    }

    #[test]
    fn starts_with() {
        let v: Vec<_, 8> = Vec::from_slice(b"ab").unwrap();
        assert!(v.starts_with(&[]));
        assert!(v.starts_with(b""));
        assert!(v.starts_with(b"a"));
        assert!(v.starts_with(b"ab"));
        assert!(!v.starts_with(b"abc"));
        assert!(!v.starts_with(b"ba"));
        assert!(!v.starts_with(b"b"));
    }

    #[test]
    fn ends_with() {
        let v: Vec<_, 8> = Vec::from_slice(b"ab").unwrap();
        assert!(v.ends_with(&[]));
        assert!(v.ends_with(b""));
        assert!(v.ends_with(b"b"));
        assert!(v.ends_with(b"ab"));
        assert!(!v.ends_with(b"abc"));
        assert!(!v.ends_with(b"ba"));
        assert!(!v.ends_with(b"a"));
    }
}

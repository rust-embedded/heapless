//! A "history buffer", similar to a write-only ring buffer of fixed length.
//!
//! This buffer keeps a fixed number of elements.  On write, the oldest element
//! is overwritten. Thus, the buffer is useful to keep a history of values with
//! some desired depth, and for example calculate a rolling average.
//!
//! # Examples
//! ```
//! use heapless::HistoryBuffer;
//!
//! // Initialize a new buffer with 8 elements.
//! let mut buf = HistoryBuffer::<_, 8>::new();
//!
//! // Starts with no data
//! assert_eq!(buf.recent(), None);
//!
//! buf.write(3);
//! buf.write(5);
//! buf.extend(&[4, 4]);
//!
//! // The most recent written element is a four.
//! assert_eq!(buf.recent(), Some(&4));
//!
//! // To access all elements in an unspecified order, use `as_slice()`.
//! for el in buf.as_slice() {
//!     println!("{:?}", el);
//! }
//!
//! // Now we can prepare an average of all values, which comes out to 4.
//! let avg = buf.as_slice().iter().sum::<usize>() / buf.len();
//! assert_eq!(avg, 4);
//! ```

use core::fmt;
use core::marker::PhantomData;
use core::mem::MaybeUninit;
use core::ops::Deref;
use core::ptr;
use core::slice;

mod storage {
    use core::mem::MaybeUninit;

    use super::{HistoryBufferInner, HistoryBufferView};

    /// Trait defining how data for a container is stored.
    ///
    /// There's two implementations available:
    ///
    /// - [`OwnedHistBufStorage`]: stores the data in an array `[T; N]` whose size is known at compile time.
    /// - [`ViewHistBufStorage`]: stores the data in an unsized `[T]`.
    ///
    /// This allows [`HistoryBuffer`] to be generic over either sized or unsized storage. The [`histbuf`]
    /// module contains a [`HistoryBufferInner`] struct that's generic on [`HistBufStorage`],
    /// and two type aliases for convenience:
    ///
    /// - [`HistBuf<T, N>`](super::HistoryBuffer) = `HistoryBufferInner<T, OwnedHistBufStorage<T, N>>`
    /// - [`HistBufView<T>`](super::HistoryBufferView) = `HistoryBufferInner<T, ViewHistBufStorage<T>>`
    ///
    /// `HistoryBuffer` can be unsized into `HistoryBufferView`, either by unsizing coercions such as `&mut HistoryBuffer -> &mut HistoryBufferView` or
    /// `Box<HistoryBuffer> -> Box<HistoryBufferView>`, or explicitly with [`.as_view()`](super::HistoryBuffer::as_view) or [`.as_mut_view()`](super::HistoryBuffer::as_mut_view).
    ///
    /// This trait is sealed, so you cannot implement it for your own types. You can only use
    /// the implementations provided by this crate.
    ///
    /// [`HistoryBufferInner`]: super::HistoryBufferInner
    /// [`HistoryBuffer`]: super::HistoryBuffer
    /// [`HistoryBufferView`]: super::HistoryBufferView
    /// [`histbuf`]: super
    #[allow(private_bounds)]
    pub trait HistBufStorage<T>: HistBufSealedStorage<T> {}

    pub trait HistBufSealedStorage<T> {
        // part of the sealed trait so that no trait is publicly implemented by `OwnedHistBufStorage` besides `Storage`
        fn borrow(&self) -> &[MaybeUninit<T>];
        fn borrow_mut(&mut self) -> &mut [MaybeUninit<T>];
        fn as_hist_buf_view(this: &HistoryBufferInner<T, Self>) -> &HistoryBufferView<T>
        where
            Self: HistBufStorage<T>;
        fn as_hist_buf_mut_view(
            this: &mut HistoryBufferInner<T, Self>,
        ) -> &mut HistoryBufferView<T>
        where
            Self: HistBufStorage<T>;
    }

    // One sealed layer of indirection to hide the internal details (The MaybeUninit).
    pub struct HistBufStorageInner<T: ?Sized> {
        pub(crate) buffer: T,
    }

    /// Implementation of [`HistBufStorage`] that stores the data in an array `[T; N]` whose size is known at compile time.
    pub type OwnedHistBufStorage<T, const N: usize> = HistBufStorageInner<[MaybeUninit<T>; N]>;
    /// Implementation of [`HistBufStorage`] that stores the data in an unsized `[T]`.
    pub type ViewHistBufStorage<T> = HistBufStorageInner<[MaybeUninit<T>]>;

    impl<T, const N: usize> HistBufSealedStorage<T> for OwnedHistBufStorage<T, N> {
        fn borrow(&self) -> &[MaybeUninit<T>] {
            &self.buffer
        }
        fn borrow_mut(&mut self) -> &mut [MaybeUninit<T>] {
            &mut self.buffer
        }
        fn as_hist_buf_view(this: &HistoryBufferInner<T, Self>) -> &HistoryBufferView<T>
        where
            Self: HistBufStorage<T>,
        {
            this
        }
        fn as_hist_buf_mut_view(this: &mut HistoryBufferInner<T, Self>) -> &mut HistoryBufferView<T>
        where
            Self: HistBufStorage<T>,
        {
            this
        }
    }
    impl<T, const N: usize> HistBufStorage<T> for OwnedHistBufStorage<T, N> {}

    impl<T> HistBufSealedStorage<T> for ViewHistBufStorage<T> {
        fn borrow(&self) -> &[MaybeUninit<T>] {
            &self.buffer
        }
        fn borrow_mut(&mut self) -> &mut [MaybeUninit<T>] {
            &mut self.buffer
        }
        fn as_hist_buf_view(this: &HistoryBufferInner<T, Self>) -> &HistoryBufferView<T>
        where
            Self: HistBufStorage<T>,
        {
            this
        }
        fn as_hist_buf_mut_view(this: &mut HistoryBufferInner<T, Self>) -> &mut HistoryBufferView<T>
        where
            Self: HistBufStorage<T>,
        {
            this
        }
    }
    impl<T> HistBufStorage<T> for ViewHistBufStorage<T> {}
}

pub use storage::{HistBufStorage, OwnedHistBufStorage, ViewHistBufStorage};

use storage::HistBufStorageInner;

use self::storage::HistBufSealedStorage;

/// Base struct for [`HistoryBuffer`] and [`HistoryBufferView`], generic over the [`HistBufStorage`].
///
/// In most cases you should use [`HistoryBuffer`] or [`HistoryBufferView`] directly. Only use this
/// struct if you want to write code that's generic over both.
pub struct HistoryBufferInner<T, S: HistBufStorage<T> + ?Sized> {
    // This phantomdata is required because otherwise rustc thinks that `T` is not used
    phantom: PhantomData<T>,
    write_at: usize,
    filled: bool,
    data: S,
}

/// A "history buffer", similar to a write-only ring buffer of fixed length.
///
/// This buffer keeps a fixed number of elements.  On write, the oldest element
/// is overwritten. Thus, the buffer is useful to keep a history of values with
/// some desired depth, and for example calculate a rolling average.
///
/// # Examples
/// ```
/// use heapless::HistoryBuffer;
///
/// // Initialize a new buffer with 8 elements.
/// let mut buf = HistoryBuffer::<_, 8>::new();
///
/// // Starts with no data
/// assert_eq!(buf.recent(), None);
///
/// buf.write(3);
/// buf.write(5);
/// buf.extend(&[4, 4]);
///
/// // The most recent written element is a four.
/// assert_eq!(buf.recent(), Some(&4));
///
/// // To access all elements in an unspecified order, use `as_slice()`.
/// for el in buf.as_slice() {
///     println!("{:?}", el);
/// }
///
/// // Now we can prepare an average of all values, which comes out to 4.
/// let avg = buf.as_slice().iter().sum::<usize>() / buf.len();
/// assert_eq!(avg, 4);
/// ```
pub type HistoryBuffer<T, const N: usize> = HistoryBufferInner<T, OwnedHistBufStorage<T, N>>;

/// A "view" into a [`HistoryBuffer`]
///
/// Unlike [`HistoryBuffer`], it doesn't have the `const N: usize` in its type signature.
///
/// # Examples
/// ```
/// use heapless::histbuf::{HistoryBuffer, HistoryBufferView};
///
/// // Initialize a new buffer with 8 elements.
/// let mut owned_buf = HistoryBuffer::<_, 8>::new();
/// let buf: &mut HistoryBufferView<_> = &mut owned_buf;
///
/// // Starts with no data
/// assert_eq!(buf.recent(), None);
///
/// buf.write(3);
/// buf.write(5);
/// buf.extend(&[4, 4]);
///
/// // The most recent written element is a four.
/// assert_eq!(buf.recent(), Some(&4));
///
/// // To access all elements in an unspecified order, use `as_slice()`.
/// for el in buf.as_slice() {
///     println!("{:?}", el);
/// }
///
/// // Now we can prepare an average of all values, which comes out to 4.
/// let avg = buf.as_slice().iter().sum::<usize>() / buf.len();
/// assert_eq!(avg, 4);
/// ```
pub type HistoryBufferView<T> = HistoryBufferInner<T, ViewHistBufStorage<T>>;

impl<T, const N: usize> HistoryBuffer<T, N> {
    const INIT: MaybeUninit<T> = MaybeUninit::uninit();

    /// Constructs a new history buffer.
    ///
    /// The construction of a `HistoryBuffer` works in `const` contexts.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::HistoryBuffer;
    ///
    /// // Allocate a 16-element buffer on the stack
    /// let x: HistoryBuffer<u8, 16> = HistoryBuffer::new();
    /// assert_eq!(x.len(), 0);
    /// ```
    #[inline]
    pub const fn new() -> Self {
        const {
            assert!(N > 0);
        }

        Self {
            phantom: PhantomData,
            data: HistBufStorageInner {
                buffer: [Self::INIT; N],
            },
            write_at: 0,
            filled: false,
        }
    }
}

impl<T, const N: usize> HistoryBuffer<T, N>
where
    T: Copy + Clone,
{
    /// Constructs a new history buffer, where every element is the given value.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::HistoryBuffer;
    ///
    /// // Allocate a 16-element buffer on the stack
    /// let mut x: HistoryBuffer<u8, 16> = HistoryBuffer::new_with(4);
    /// // All elements are four
    /// assert_eq!(x.as_slice(), [4; 16]);
    /// ```
    #[inline]
    pub fn new_with(t: T) -> Self {
        Self {
            phantom: PhantomData,
            data: HistBufStorageInner {
                buffer: [MaybeUninit::new(t); N],
            },
            write_at: 0,
            filled: true,
        }
    }
}
impl<T: Copy, S: HistBufStorage<T> + ?Sized> HistoryBufferInner<T, S> {
    /// Get a reference to the `HistoryBuffer`, erasing the `N` const-generic.
    #[inline]
    pub fn as_view(&self) -> &HistoryBufferView<T> {
        S::as_hist_buf_view(self)
    }

    /// Get a mutable reference to the `HistoryBuffer`, erasing the `N` const-generic.
    #[inline]
    pub fn as_mut_view(&mut self) -> &mut HistoryBufferView<T> {
        S::as_hist_buf_mut_view(self)
    }
    /// Clears the buffer, replacing every element with the given value.
    pub fn clear_with(&mut self, t: T) {
        // SAFETY: we reset the values just after
        unsafe { self.drop_contents() };
        self.write_at = 0;
        self.filled = true;

        for d in self.data.borrow_mut() {
            *d = MaybeUninit::new(t);
        }
    }
}

impl<T, S: HistBufStorage<T> + ?Sized> HistoryBufferInner<T, S> {
    /// Clears the buffer
    pub fn clear(&mut self) {
        // SAFETY: we reset the values just after
        unsafe { self.drop_contents() };
        self.write_at = 0;
        self.filled = false;
    }
}

impl<T, S: HistBufStorage<T> + ?Sized> HistoryBufferInner<T, S> {
    unsafe fn drop_contents(&mut self) {
        unsafe {
            ptr::drop_in_place(ptr::slice_from_raw_parts_mut(
                self.data.borrow_mut().as_mut_ptr().cast::<T>(),
                self.len(),
            ));
        }
    }

    /// Returns the current fill level of the buffer.
    #[inline]
    pub fn len(&self) -> usize {
        if self.filled {
            self.capacity()
        } else {
            self.write_at
        }
    }

    /// Returns true if the buffer is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::HistoryBuffer;
    ///
    /// let x: HistoryBuffer<u8, 16> = HistoryBuffer::new();
    /// assert!(x.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the capacity of the buffer, which is the length of the
    /// underlying backing array.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.data.borrow().len()
    }

    /// Returns whether the buffer is full
    #[inline]
    pub fn is_full(&self) -> bool {
        self.filled
    }

    /// Writes an element to the buffer, overwriting the oldest value.
    pub fn write(&mut self, t: T) {
        if self.filled {
            // Drop the old before we overwrite it.
            unsafe { ptr::drop_in_place(self.data.borrow_mut()[self.write_at].as_mut_ptr()) }
        }
        self.data.borrow_mut()[self.write_at] = MaybeUninit::new(t);

        self.write_at += 1;
        if self.write_at == self.capacity() {
            self.write_at = 0;
            self.filled = true;
        }
    }

    /// Clones and writes all elements in a slice to the buffer.
    ///
    /// If the slice is longer than the buffer, only the last `self.len()`
    /// elements will actually be stored.
    pub fn extend_from_slice(&mut self, other: &[T])
    where
        T: Clone,
    {
        for item in other {
            self.write(item.clone());
        }
    }

    /// Returns a reference to the most recently written value.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::HistoryBuffer;
    ///
    /// let mut x: HistoryBuffer<u8, 16> = HistoryBuffer::new();
    /// x.write(4);
    /// x.write(10);
    /// assert_eq!(x.recent(), Some(&10));
    /// ```
    pub fn recent(&self) -> Option<&T> {
        self.recent_index()
            .map(|i| unsafe { &*self.data.borrow()[i].as_ptr() })
    }

    /// Returns index of the most recently written value in the underlying slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::HistoryBuffer;
    ///
    /// let mut x: HistoryBuffer<u8, 16> = HistoryBuffer::new();
    /// x.write(4);
    /// x.write(10);
    /// assert_eq!(x.recent_index(), Some(1));
    /// ```
    pub fn recent_index(&self) -> Option<usize> {
        if self.write_at == 0 {
            if self.filled {
                Some(self.capacity() - 1)
            } else {
                None
            }
        } else {
            Some(self.write_at - 1)
        }
    }

    /// Returns a reference to the oldest value in the buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::HistoryBuffer;
    ///
    /// let mut x: HistoryBuffer<u8, 16> = HistoryBuffer::new();
    /// x.write(4);
    /// x.write(10);
    /// assert_eq!(x.oldest(), Some(&4));
    /// ```
    pub fn oldest(&self) -> Option<&T> {
        self.oldest_index()
            .map(|i| unsafe { &*self.data.borrow()[i].as_ptr() })
    }

    /// Returns index of the oldest value in the underlying slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::HistoryBuffer;
    ///
    /// let mut x: HistoryBuffer<u8, 16> = HistoryBuffer::new();
    /// x.write(4);
    /// x.write(10);
    /// assert_eq!(x.oldest_index(), Some(0));
    /// ```
    pub fn oldest_index(&self) -> Option<usize> {
        if self.filled {
            Some(self.write_at)
        } else if self.write_at == 0 {
            None
        } else {
            Some(0)
        }
    }

    /// Returns the array slice backing the buffer, without keeping track
    /// of the write position. Therefore, the element order is unspecified.
    pub fn as_slice(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.data.borrow().as_ptr().cast(), self.len()) }
    }

    /// Returns a pair of slices which contain, in order, the contents of the buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::HistoryBuffer;
    ///
    /// let mut buffer: HistoryBuffer<u8, 6> = HistoryBuffer::new();
    /// buffer.extend([0, 0, 0]);
    /// buffer.extend([1, 2, 3, 4, 5, 6]);
    /// assert_eq!(buffer.as_slices(), (&[1, 2, 3][..], &[4, 5, 6][..]));
    /// ```
    pub fn as_slices(&self) -> (&[T], &[T]) {
        let buffer = self.as_slice();

        if self.filled {
            (&buffer[self.write_at..], &buffer[..self.write_at])
        } else {
            (buffer, &[])
        }
    }

    /// Returns a reference to the element in the order from oldest to newest.
    ///
    /// `buf.ordered_get(0)` will always return the oldest element in the buffer.
    ///
    /// `buf.ordered_get(buf.len() - 1)` will always return the newest element
    /// in the buffer.
    ///
    /// Returns None if `index >= self.len()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::HistoryBuffer;
    ///
    /// let mut buffer: HistoryBuffer<u8, 6> = HistoryBuffer::new();
    /// buffer.extend([0, 0, 0]);
    /// buffer.extend([1, 2, 3, 4, 5, 6]);
    /// assert_eq!(buffer.ordered_get(0), Some(&1u8));
    /// assert_eq!(buffer.ordered_get(1), Some(&2u8));
    /// assert_eq!(buffer.ordered_get(2), Some(&3u8));
    /// assert_eq!(buffer.ordered_get(6), None);
    /// ```
    pub fn ordered_get(&self, idx: usize) -> Option<&T> {
        self.oldest_ordered().nth(idx)
    }

    /// Returns double ended iterator for iterating over the buffer from
    /// the oldest to the newest and back.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::HistoryBuffer;
    ///
    /// let mut buffer: HistoryBuffer<u8, 6> = HistoryBuffer::new();
    /// buffer.extend([0, 0, 0, 1, 2, 3, 4, 5, 6]);
    /// let expected = [1, 2, 3, 4, 5, 6];
    /// for (x, y) in buffer.oldest_ordered().zip(expected.iter()) {
    ///     assert_eq!(x, y)
    /// }
    /// ```
    pub fn oldest_ordered(&self) -> OldestOrderedInner<'_, T, S> {
        let (old, new) = self.as_slices();
        OldestOrderedInner {
            phantom: PhantomData,
            inner: old.iter().chain(new),
        }
    }
}

impl<T, S: HistBufStorage<T> + ?Sized> Extend<T> for HistoryBufferInner<T, S> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        for item in iter.into_iter() {
            self.write(item);
        }
    }
}

impl<'a, T, S: HistBufStorage<T> + ?Sized> Extend<&'a T> for HistoryBufferInner<T, S>
where
    T: 'a + Clone,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = &'a T>,
    {
        self.extend(iter.into_iter().cloned());
    }
}

impl<T, const N: usize> Clone for HistoryBuffer<T, N>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        let mut ret = Self::new();
        for (new, old) in ret.data.borrow_mut().iter_mut().zip(self.as_slice()) {
            new.write(old.clone());
        }
        ret.filled = self.filled;
        ret.write_at = self.write_at;
        ret
    }
}

impl<T, S: HistBufStorage<T> + ?Sized> Drop for HistoryBufferInner<T, S> {
    fn drop(&mut self) {
        unsafe { self.drop_contents() }
    }
}

impl<T, S: HistBufStorage<T> + ?Sized> Deref for HistoryBufferInner<T, S> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, S: HistBufStorage<T> + ?Sized> AsRef<[T]> for HistoryBufferInner<T, S> {
    #[inline]
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T, S: HistBufStorage<T> + ?Sized> fmt::Debug for HistoryBufferInner<T, S>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <[T] as fmt::Debug>::fmt(self, f)
    }
}

impl<T, const N: usize> Default for HistoryBuffer<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, S: HistBufStorage<T> + ?Sized> PartialEq for HistoryBufferInner<T, S>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.oldest_ordered().eq(other.oldest_ordered())
    }
}

/// Base struct for [`OldestOrdered`] and [`OldestOrderedView`], generic over the [`HistBufStorage`].
///
/// In most cases you should use [`OldestOrdered`] or [`OldestOrderedView`] directly. Only use this
/// struct if you want to write code that's generic over both.
pub struct OldestOrderedInner<'a, T, S: HistBufStorage<T> + ?Sized> {
    phantom: PhantomData<S>,
    inner: core::iter::Chain<core::slice::Iter<'a, T>, core::slice::Iter<'a, T>>,
}

/// Double ended iterator on the underlying buffer ordered from the oldest data
/// to the newest.
///
/// This type exists for backwards compatibility. It is always better to convert it to an [`OldestOrderedView`] with [`into_view`](OldestOrdered::into_view)
pub type OldestOrdered<'a, T, const N: usize> =
    OldestOrderedInner<'a, T, OwnedHistBufStorage<T, N>>;

/// Double ended iterator on the underlying buffer ordered from the oldest data
/// to the newest
pub type OldestOrderedView<'a, T> = OldestOrderedInner<'a, T, ViewHistBufStorage<T>>;

impl<'a, T, const N: usize> OldestOrdered<'a, T, N> {
    /// Remove the `N` const-generic parameter from the iterator
    ///
    /// For the opposite operation, see [`into_legacy_iter`](OldestOrderedView::into_legacy_iter)
    pub fn into_view(self) -> OldestOrderedView<'a, T> {
        OldestOrderedView {
            phantom: PhantomData,
            inner: self.inner,
        }
    }
}

impl<'a, T> OldestOrderedView<'a, T> {
    /// Add back the `N` const-generic parameter to use it with APIs expecting the legacy type
    ///
    /// You probably do not need this
    ///
    /// For the opposite operation, see [`into_view`](OldestOrdered::into_view)
    pub fn into_legacy_iter<const N: usize>(self) -> OldestOrdered<'a, T, N> {
        OldestOrdered {
            phantom: PhantomData,
            inner: self.inner,
        }
    }
}

impl<T, S: HistBufStorage<T> + ?Sized> Clone for OldestOrderedInner<'_, T, S> {
    fn clone(&self) -> Self {
        Self {
            phantom: PhantomData,
            inner: self.inner.clone(),
        }
    }
}

impl<'a, T, S: HistBufStorage<T> + ?Sized> Iterator for OldestOrderedInner<'a, T, S> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<T, const N: usize> DoubleEndedIterator for OldestOrdered<'_, T, N> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

#[cfg(test)]
mod tests {
    use core::fmt::Debug;
    use core::sync::atomic::{AtomicUsize, Ordering};

    use static_assertions::assert_not_impl_any;

    use super::{HistoryBuffer, HistoryBufferView};

    // Ensure a `HistoryBuffer` containing `!Send` values stays `!Send` itself.
    assert_not_impl_any!(HistoryBuffer<*const (), 4>: Send);

    #[test]
    fn new() {
        let x: HistoryBuffer<u8, 4> = HistoryBuffer::new_with(1);
        assert_eq!(x.len(), 4);
        assert_eq!(x.as_slice(), [1; 4]);
        assert_eq!(*x, [1; 4]);
        assert!(x.is_full());

        let x: HistoryBuffer<u8, 4> = HistoryBuffer::new();
        assert_eq!(x.as_slice(), []);
        assert!(!x.is_full());
    }

    #[test]
    fn write() {
        let mut x: HistoryBuffer<u8, 4> = HistoryBuffer::new();
        x.write(1);
        x.write(4);
        assert_eq!(x.as_slice(), [1, 4]);

        x.write(5);
        x.write(6);
        x.write(10);
        assert_eq!(x.as_slice(), [10, 4, 5, 6]);

        x.extend([11, 12].iter());
        assert_eq!(x.as_slice(), [10, 11, 12, 6]);
    }

    #[test]
    fn clear() {
        let mut x: HistoryBuffer<u8, 4> = HistoryBuffer::new_with(1);
        x.clear();
        assert_eq!(x.as_slice(), []);

        let mut x: HistoryBuffer<u8, 4> = HistoryBuffer::new();
        x.clear_with(1);
        assert_eq!(x.as_slice(), [1; 4]);
    }

    #[test]
    fn clone() {
        let mut x: HistoryBuffer<u8, 3> = HistoryBuffer::new();
        for i in 0..10 {
            assert_eq!(x.as_slice(), x.clone().as_slice());
            x.write(i);
        }

        // Records number of clones locally and globally.
        static GLOBAL: AtomicUsize = AtomicUsize::new(0);
        #[derive(Default, PartialEq, Debug)]
        struct InstrumentedClone(usize);

        impl Clone for InstrumentedClone {
            fn clone(&self) -> Self {
                GLOBAL.fetch_add(1, Ordering::Relaxed);
                Self(self.0 + 1)
            }
        }

        let mut y: HistoryBuffer<InstrumentedClone, 2> = HistoryBuffer::new();
        let _ = y.clone();
        assert_eq!(GLOBAL.load(Ordering::Relaxed), 0);
        y.write(InstrumentedClone(0));
        assert_eq!(GLOBAL.load(Ordering::Relaxed), 0);
        assert_eq!(y.clone().as_slice(), [InstrumentedClone(1)]);
        assert_eq!(GLOBAL.load(Ordering::Relaxed), 1);
        y.write(InstrumentedClone(0));
        assert_eq!(GLOBAL.load(Ordering::Relaxed), 1);
        assert_eq!(
            y.clone().as_slice(),
            [InstrumentedClone(1), InstrumentedClone(1)]
        );
        assert_eq!(GLOBAL.load(Ordering::Relaxed), 3);
        assert_eq!(
            y.clone().clone().clone().as_slice(),
            [InstrumentedClone(3), InstrumentedClone(3)]
        );
        assert_eq!(GLOBAL.load(Ordering::Relaxed), 9);
    }

    #[test]
    fn recent() {
        let mut x: HistoryBuffer<u8, 4> = HistoryBuffer::new();
        assert_eq!(x.recent_index(), None);
        assert_eq!(x.recent(), None);

        x.write(1);
        x.write(4);
        assert_eq!(x.recent_index(), Some(1));
        assert_eq!(x.recent(), Some(&4));

        x.write(5);
        x.write(6);
        x.write(10);
        assert_eq!(x.recent_index(), Some(0));
        assert_eq!(x.recent(), Some(&10));
    }

    #[test]
    fn oldest() {
        let mut x: HistoryBuffer<u8, 4> = HistoryBuffer::new();
        assert_eq!(x.oldest_index(), None);
        assert_eq!(x.oldest(), None);

        x.write(1);
        x.write(4);
        assert_eq!(x.oldest_index(), Some(0));
        assert_eq!(x.oldest(), Some(&1));

        x.write(5);
        x.write(6);
        x.write(10);
        assert_eq!(x.oldest_index(), Some(1));
        assert_eq!(x.oldest(), Some(&4));
    }

    #[test]
    fn as_slice() {
        let mut x: HistoryBuffer<u8, 4> = HistoryBuffer::new();

        assert_eq!(x.as_slice(), []);

        x.extend([1, 2, 3, 4, 5].iter());

        assert_eq!(x.as_slice(), [5, 2, 3, 4]);
    }

    /// Test whether `.as_slices()` behaves as expected.
    #[test]
    fn as_slices() {
        let mut buffer: HistoryBuffer<u8, 4> = HistoryBuffer::new();
        let mut extend_then_assert = |extend: &[u8], assert: (&[u8], &[u8])| {
            buffer.extend(extend);
            assert_eq!(buffer.as_slices(), assert);
        };

        extend_then_assert(b"a", (b"a", b""));
        extend_then_assert(b"bcd", (b"abcd", b""));
        extend_then_assert(b"efg", (b"d", b"efg"));
        extend_then_assert(b"h", (b"efgh", b""));
        extend_then_assert(b"123456", (b"34", b"56"));
    }

    /// Test whether `.as_slices()` and `.oldest_ordered()` produce elements in the same order.
    #[test]
    fn as_slices_equals_ordered() {
        let mut buffer: HistoryBuffer<u8, 6> = HistoryBuffer::new();

        for n in 0..20 {
            buffer.write(n);
            let (head, tail) = buffer.as_slices();
            assert_eq_iter(
                [head, tail].iter().copied().flatten(),
                buffer.oldest_ordered(),
            );
        }
    }

    #[test]
    fn ordered_get() {
        let mut buffer: HistoryBuffer<u8, 6> = HistoryBuffer::new();
        assert_eq!(buffer.ordered_get(0), None);

        buffer.write(1u8);
        assert_eq!(buffer.ordered_get(0), Some(&1u8));

        buffer.write(2u8);
        assert_eq!(buffer.ordered_get(0), Some(&1u8));
        assert_eq!(buffer.ordered_get(1), Some(&2u8));

        buffer.extend([3, 4, 5, 6, 7, 8]);
        assert_eq!(buffer.ordered_get(0), Some(&3u8));
        assert_eq!(buffer.ordered_get(5), Some(&8u8));
        assert_eq!(buffer.ordered_get(6), None);
    }

    #[test]
    fn ordered() {
        // test on an empty buffer
        let buffer: HistoryBuffer<u8, 6> = HistoryBuffer::new();
        let mut iter = buffer.oldest_ordered();
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
        assert_eq!(iter.next_back(), None);

        // test on a un-filled buffer
        let mut buffer: HistoryBuffer<u8, 6> = HistoryBuffer::new();
        buffer.extend([1, 2, 3]);
        assert_eq!(buffer.len(), 3);
        assert_eq_iter(buffer.oldest_ordered(), &[1, 2, 3]);
        assert_eq_iter(buffer.oldest_ordered().rev(), &[3, 2, 1]);
        let mut iter = buffer.oldest_ordered();
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next_back(), Some(&3));
        assert_eq!(iter.next_back(), Some(&2));
        assert_eq!(iter.next_back(), None);
        assert_eq!(iter.next(), None);

        // test on an exactly filled buffer
        let mut buffer: HistoryBuffer<u8, 6> = HistoryBuffer::new();
        buffer.extend([1, 2, 3, 4, 5, 6]);
        assert_eq!(buffer.len(), 6);
        assert_eq_iter(buffer.oldest_ordered(), &[1, 2, 3, 4, 5, 6]);
        assert_eq_iter(buffer.oldest_ordered().rev(), &[6, 5, 4, 3, 2, 1]);

        // test on a filled buffer
        let mut buffer: HistoryBuffer<u8, 6> = HistoryBuffer::new();
        buffer.extend([0, 0, 0, 1, 2, 3, 4, 5, 6]);
        assert_eq!(buffer.len(), 6);
        assert_eq_iter(buffer.oldest_ordered(), &[1, 2, 3, 4, 5, 6]);
        assert_eq_iter(buffer.oldest_ordered().rev(), &[6, 5, 4, 3, 2, 1]);

        // comprehensive test all cases
        for n in 0..50 {
            const N: usize = 7;
            let mut buffer: HistoryBuffer<u8, N> = HistoryBuffer::new();
            buffer.extend(0..n);
            assert_eq_iter(
                buffer.oldest_ordered().copied(),
                n.saturating_sub(N as u8)..n,
            );
            assert_eq_iter(
                buffer.oldest_ordered().rev().copied(),
                (n.saturating_sub(N as u8)..n).rev(),
            );
        }
    }

    /// Compares two iterators item by item, making sure they stop at the same time.
    fn assert_eq_iter<I: Eq + Debug>(
        a: impl IntoIterator<Item = I>,
        b: impl IntoIterator<Item = I>,
    ) {
        let mut a = a.into_iter();
        let mut b = b.into_iter();

        let mut i = 0;
        loop {
            let a_item = a.next();
            let b_item = b.next();

            assert_eq!(a_item, b_item, "{}", i);

            i += 1;

            if b_item.is_none() {
                break;
            }
        }
    }

    #[test]
    fn partial_eq() {
        let mut x: HistoryBuffer<u8, 3> = HistoryBuffer::new();
        let mut y: HistoryBuffer<u8, 3> = HistoryBuffer::new();
        assert_eq!(x, y);
        x.write(1);
        assert_ne!(x, y);
        y.write(1);
        assert_eq!(x, y);
        for _ in 0..4 {
            x.write(2);
            assert_ne!(x, y);
            for i in 0..5 {
                x.write(i);
                y.write(i);
            }
            assert_eq!(
                x,
                y,
                "{:?} {:?}",
                x.iter().collect::<Vec<_>>(),
                y.iter().collect::<Vec<_>>()
            );
        }
    }

    #[test]
    fn clear_drops_values() {
        static DROP_COUNT: AtomicUsize = AtomicUsize::new(0);

        struct DropCheck {}

        impl Drop for DropCheck {
            fn drop(&mut self) {
                DROP_COUNT.fetch_add(1, Ordering::SeqCst);
            }
        }

        let mut x: HistoryBuffer<DropCheck, 3> = HistoryBuffer::new();
        x.write(DropCheck {});
        x.write(DropCheck {});
        x.write(DropCheck {});

        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 0);
        x.clear();
        assert_eq!(DROP_COUNT.load(Ordering::SeqCst), 3);
    }

    fn _test_variance<'a: 'b, 'b>(x: HistoryBuffer<&'a (), 42>) -> HistoryBuffer<&'b (), 42> {
        x
    }
    fn _test_variance_view<'a: 'b, 'b, 'c>(
        x: &'c HistoryBufferView<&'a ()>,
    ) -> &'c HistoryBufferView<&'b ()> {
        x
    }
}

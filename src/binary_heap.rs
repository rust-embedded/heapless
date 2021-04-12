//! A priority queue implemented with a binary heap.
//!
//! Insertion and popping the largest element have `O(log n)` time complexity. Checking the largest
//! / smallest element is `O(1)`.

// TODO not yet implemented
// Converting a vector to a binary heap can be done in-place, and has `O(n)` complexity. A binary
// heap can also be converted to a sorted vector in-place, allowing it to be used for an `O(n log
// n)` in-place heapsort.

use core::{
    fmt,
    marker::PhantomData,
    mem::{self, ManuallyDrop},
    ops::{Deref, DerefMut},
    ptr, slice,
};

use crate::sealed::{binary_heap::Kind, spsc::Uxx};
use crate::vec::VecBase;

/// Min-heap
pub enum Min {}

/// Max-heap
pub enum Max {}

/// A priority queue implemented with a binary heap.
///
/// This can be either a min-heap or a max-heap.
///
/// It is a logic error for an item to be modified in such a way that the item's ordering relative
/// to any other item, as determined by the `Ord` trait, changes while it is in the heap. This is
/// normally only possible through `Cell`, `RefCell`, global state, I/O, or unsafe code.

pub struct BinaryHeapBase<T, K, U: Uxx, const N: usize> {
    pub(crate) _kind: PhantomData<K>,
    pub(crate) data: VecBase<T, U, N>,
}

/// A `BinaryHeapBase` with a length type of `usize`.
///
/// ```
/// use heapless::binary_heap::{BinaryHeap, Max};
///
/// let mut heap: BinaryHeap<_, Max, 8> = BinaryHeap::new();
///
/// // We can use peek to look at the next item in the heap. In this case,
/// // there's no items in there yet so we get None.
/// assert_eq!(heap.peek(), None);
///
/// // Let's add some scores...
/// heap.push(1).unwrap();
/// heap.push(5).unwrap();
/// heap.push(2).unwrap();
///
/// // Now peek shows the most important item in the heap.
/// assert_eq!(heap.peek(), Some(&5));
///
/// // We can check the length of a heap.
/// assert_eq!(heap.len(), 3);
///
/// // We can iterate over the items in the heap, although they are returned in
/// // a random order.
/// for x in &heap {
///     println!("{}", x);
/// }
///
/// // If we instead pop these scores, they should come back in order.
/// assert_eq!(heap.pop(), Some(5));
/// assert_eq!(heap.pop(), Some(2));
/// assert_eq!(heap.pop(), Some(1));
/// assert_eq!(heap.pop(), None);
///
/// // We can clear the heap of any remaining items.
/// heap.clear();
///
/// // The heap should now be empty.
/// assert!(heap.is_empty())
/// ```
pub type BinaryHeap<T, K, const N: usize> = BinaryHeapBase<T, K, usize, N>;

macro_rules! impl_new {
    ($Uxx:ident, $name:ident, $doc:tt) => {
        impl<T, K, const N: usize> BinaryHeapBase<T, K, $Uxx, N> {
            /* Constructors */
            #[doc = $doc]
            pub const fn $name() -> Self {
                Self {
                    _kind: PhantomData,
                    data: VecBase::$name(),
                }
            }
        }
    };
}

impl_new!(
    u8,
    u8,
    "Creates an empty BinaryHeap as a $K-heap. **Safety**: Assumes `N <= u8::MAX`."
);
impl_new!(
    u16,
    u16,
    "Creates an empty BinaryHeap as a $K-heap. **Safety**: Assumes `N <= u16::MAX`."
);

impl<T, K, const N: usize> BinaryHeap<T, K, N> {
    /* Constructors */
    /// Creates an empty BinaryHeap as a $K-heap.
    ///
    /// ```
    /// use heapless::binary_heap::{BinaryHeap, Max};
    ///
    /// // allocate the binary heap on the stack
    /// let mut heap: BinaryHeap<_, Max, 8> = BinaryHeap::new();
    /// heap.push(4).unwrap();
    ///
    /// // allocate the binary heap in a static variable
    /// static mut HEAP: BinaryHeap<i32, Max, 8> = BinaryHeap::new();
    /// ```
    pub const fn new() -> Self {
        Self {
            _kind: PhantomData,
            data: VecBase::new(),
        }
    }
}

impl<T, K, U: Uxx, const N: usize> BinaryHeapBase<T, K, U, N>
where
    T: Ord,
    K: Kind,
{
    /* Public API */
    /// Returns the capacity of the binary heap.
    pub fn capacity(&self) -> usize {
        self.data.capacity_nonconst()
    }

    /// Drops all items from the binary heap.
    ///
    /// ```
    /// use heapless::binary_heap::{BinaryHeap, Max};
    ///
    /// let mut heap: BinaryHeap<_, Max, 8> = BinaryHeap::new();
    /// heap.push(1).unwrap();
    /// heap.push(3).unwrap();
    ///
    /// assert!(!heap.is_empty());
    ///
    /// heap.clear();
    ///
    /// assert!(heap.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.data.clear()
    }

    /// Returns the length of the binary heap.
    ///
    /// ```
    /// use heapless::binary_heap::{BinaryHeap, Max};
    ///
    /// let mut heap: BinaryHeap<_, Max, 8> = BinaryHeap::new();
    /// heap.push(1).unwrap();
    /// heap.push(3).unwrap();
    ///
    /// assert_eq!(heap.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Checks if the binary heap is empty.
    ///
    /// ```
    /// use heapless::binary_heap::{BinaryHeap, Max};
    ///
    /// let mut heap: BinaryHeap<_, Max, 8> = BinaryHeap::new();
    ///
    /// assert!(heap.is_empty());
    ///
    /// heap.push(3).unwrap();
    /// heap.push(5).unwrap();
    /// heap.push(1).unwrap();
    ///
    /// assert!(!heap.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns an iterator visiting all values in the underlying vector, in arbitrary order.
    ///
    /// ```
    /// use heapless::binary_heap::{BinaryHeap, Max};
    ///
    /// let mut heap: BinaryHeap<_, Max, 8> = BinaryHeap::new();
    /// heap.push(1).unwrap();
    /// heap.push(2).unwrap();
    /// heap.push(3).unwrap();
    /// heap.push(4).unwrap();
    ///
    /// // Print 1, 2, 3, 4 in arbitrary order
    /// for x in heap.iter() {
    ///     println!("{}", x);
    ///
    /// }
    /// ```
    pub fn iter(&self) -> slice::Iter<'_, T> {
        self.data.as_slice().iter()
    }

    /// Returns a mutable iterator visiting all values in the underlying vector, in arbitrary order.
    ///
    /// **WARNING** Mutating the items in the binary heap can leave the heap in an inconsistent
    /// state.
    pub fn iter_mut(&mut self) -> slice::IterMut<'_, T> {
        self.data.as_mut_slice().iter_mut()
    }

    /// Returns the *top* (greatest if max-heap, smallest if min-heap) item in the binary heap, or
    /// None if it is empty.
    ///
    /// ```
    /// use heapless::binary_heap::{BinaryHeap, Max};
    ///
    /// let mut heap: BinaryHeap<_, Max, 8> = BinaryHeap::new();
    /// assert_eq!(heap.peek(), None);
    ///
    /// heap.push(1).unwrap();
    /// heap.push(5).unwrap();
    /// heap.push(2).unwrap();
    /// assert_eq!(heap.peek(), Some(&5));
    /// ```
    pub fn peek(&self) -> Option<&T> {
        self.data.as_slice().get(0)
    }

    /// Returns a mutable reference to the greatest item in the binary heap, or
    /// `None` if it is empty.
    ///
    /// Note: If the `PeekMut` value is leaked, the heap may be in an
    /// inconsistent state.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::binary_heap::{BinaryHeap, Max};
    ///
    /// let mut heap: BinaryHeap<_, Max, 8> = BinaryHeap::new();
    /// assert!(heap.peek_mut().is_none());
    ///
    /// heap.push(1);
    /// heap.push(5);
    /// heap.push(2);
    /// {
    ///     let mut val = heap.peek_mut().unwrap();
    ///     *val = 0;
    /// }
    ///
    /// assert_eq!(heap.peek(), Some(&2));
    /// ```
    pub fn peek_mut(&mut self) -> Option<PeekMut<'_, T, K, U, N>> {
        if self.is_empty() {
            None
        } else {
            Some(PeekMut {
                heap: self,
                sift: true,
            })
        }
    }

    /// Removes the *top* (greatest if max-heap, smallest if min-heap) item from the binary heap and
    /// returns it, or None if it is empty.
    ///
    /// ```
    /// use heapless::binary_heap::{BinaryHeap, Max};
    ///
    /// let mut heap: BinaryHeap<_, Max, 8> = BinaryHeap::new();
    /// heap.push(1).unwrap();
    /// heap.push(3).unwrap();
    ///
    /// assert_eq!(heap.pop(), Some(3));
    /// assert_eq!(heap.pop(), Some(1));
    /// assert_eq!(heap.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            Some(unsafe { self.pop_unchecked() })
        }
    }

    /// Removes the *top* (greatest if max-heap, smallest if min-heap) item from the binary heap and
    /// returns it, without checking if the binary heap is empty.
    pub unsafe fn pop_unchecked(&mut self) -> T {
        let mut item = self.data.pop_unchecked();

        if !self.is_empty() {
            mem::swap(&mut item, self.data.as_mut_slice().get_unchecked_mut(0));
            self.sift_down_to_bottom(0);
        }
        item
    }

    /// Pushes an item onto the binary heap.
    ///
    /// ```
    /// use heapless::binary_heap::{BinaryHeap, Max};
    ///
    /// let mut heap: BinaryHeap<_, Max, 8> = BinaryHeap::new();
    /// heap.push(3).unwrap();
    /// heap.push(5).unwrap();
    /// heap.push(1).unwrap();
    ///
    /// assert_eq!(heap.len(), 3);
    /// assert_eq!(heap.peek(), Some(&5));
    /// ```
    pub fn push(&mut self, item: T) -> Result<(), T> {
        if self.data.is_full() {
            return Err(item);
        }

        unsafe { self.push_unchecked(item) }
        Ok(())
    }

    /// Pushes an item onto the binary heap without first checking if it's full.
    pub unsafe fn push_unchecked(&mut self, item: T) {
        let old_len = self.len();
        self.data.push_unchecked(item);
        self.sift_up(0, old_len);
    }

    /* Private API */
    fn sift_down_to_bottom(&mut self, mut pos: usize) {
        let end = self.len();
        let start = pos;
        unsafe {
            let mut hole = Hole::new(self.data.as_mut_slice(), pos);
            let mut child = 2 * pos + 1;
            while child < end {
                let right = child + 1;
                // compare with the greater of the two children
                if right < end && hole.get(child).cmp(hole.get(right)) != K::ordering() {
                    child = right;
                }
                hole.move_to(child);
                child = 2 * hole.pos() + 1;
            }
            pos = hole.pos;
        }
        self.sift_up(start, pos);
    }

    fn sift_up(&mut self, start: usize, pos: usize) -> usize {
        unsafe {
            // Take out the value at `pos` and create a hole.
            let mut hole = Hole::new(self.data.as_mut_slice(), pos);

            while hole.pos() > start {
                let parent = (hole.pos() - 1) / 2;
                if hole.element().cmp(hole.get(parent)) != K::ordering() {
                    break;
                }
                hole.move_to(parent);
            }
            hole.pos()
        }
    }
}

/// Hole represents a hole in a slice i.e. an index without valid value
/// (because it was moved from or duplicated).
/// In drop, `Hole` will restore the slice by filling the hole
/// position with the value that was originally removed.
struct Hole<'a, T> {
    data: &'a mut [T],
    /// `elt` is always `Some` from new until drop.
    elt: ManuallyDrop<T>,
    pos: usize,
}

impl<'a, T> Hole<'a, T> {
    /// Create a new Hole at index `pos`.
    ///
    /// Unsafe because pos must be within the data slice.
    #[inline]
    unsafe fn new(data: &'a mut [T], pos: usize) -> Self {
        debug_assert!(pos < data.len());
        let elt = ptr::read(data.get_unchecked(pos));
        Hole {
            data,
            elt: ManuallyDrop::new(elt),
            pos,
        }
    }

    #[inline]
    fn pos(&self) -> usize {
        self.pos
    }

    /// Returns a reference to the element removed.
    #[inline]
    fn element(&self) -> &T {
        &self.elt
    }

    /// Returns a reference to the element at `index`.
    ///
    /// Unsafe because index must be within the data slice and not equal to pos.
    #[inline]
    unsafe fn get(&self, index: usize) -> &T {
        debug_assert!(index != self.pos);
        debug_assert!(index < self.data.len());
        self.data.get_unchecked(index)
    }

    /// Move hole to new location
    ///
    /// Unsafe because index must be within the data slice and not equal to pos.
    #[inline]
    unsafe fn move_to(&mut self, index: usize) {
        debug_assert!(index != self.pos);
        debug_assert!(index < self.data.len());
        let index_ptr: *const _ = self.data.get_unchecked(index);
        let hole_ptr = self.data.get_unchecked_mut(self.pos);
        ptr::copy_nonoverlapping(index_ptr, hole_ptr, 1);
        self.pos = index;
    }
}

/// Structure wrapping a mutable reference to the greatest item on a
/// `BinaryHeapBase`.
///
/// This `struct` is created by the [`peek_mut`] method on [`BinaryHeapBase`]. See
/// its documentation for more.
///
/// [`peek_mut`]: struct.BinaryHeapBase.html#method.peek_mut
/// [`BinaryHeap`]: struct.BinaryHeapBase.html
pub struct PeekMut<'a, T, K, U: Uxx, const N: usize>
where
    T: Ord,
    K: Kind,
{
    heap: &'a mut BinaryHeapBase<T, K, U, N>,
    sift: bool,
}

impl<T, K, U: Uxx, const N: usize> Drop for PeekMut<'_, T, K, U, N>
where
    T: Ord,
    K: Kind,
{
    fn drop(&mut self) {
        if self.sift {
            self.heap.sift_down_to_bottom(0);
        }
    }
}

impl<T, K, U: Uxx, const N: usize> Deref for PeekMut<'_, T, K, U, N>
where
    T: Ord,
    K: Kind,
{
    type Target = T;
    fn deref(&self) -> &T {
        debug_assert!(!self.heap.is_empty());
        // SAFE: PeekMut is only instantiated for non-empty heaps
        unsafe { self.heap.data.as_slice().get_unchecked(0) }
    }
}

impl<T, K, U: Uxx, const N: usize> DerefMut for PeekMut<'_, T, K, U, N>
where
    T: Ord,
    K: Kind,
{
    fn deref_mut(&mut self) -> &mut T {
        debug_assert!(!self.heap.is_empty());
        // SAFE: PeekMut is only instantiated for non-empty heaps
        unsafe { self.heap.data.as_mut_slice().get_unchecked_mut(0) }
    }
}

impl<'a, T, K, U: Uxx, const N: usize> PeekMut<'a, T, K, U, N>
where
    T: Ord,
    K: Kind,
{
    /// Removes the peeked value from the heap and returns it.
    pub fn pop(mut this: PeekMut<'a, T, K, U, N>) -> T {
        let value = this.heap.pop().unwrap();
        this.sift = false;
        value
    }
}

impl<'a, T> Drop for Hole<'a, T> {
    #[inline]
    fn drop(&mut self) {
        // fill the hole again
        unsafe {
            let pos = self.pos;
            ptr::write(self.data.get_unchecked_mut(pos), ptr::read(&*self.elt));
        }
    }
}

impl<T, K, U: Uxx, const N: usize> Default for BinaryHeapBase<T, K, U, N>
where
    T: Ord,
    K: Kind,
{
    fn default() -> Self {
        BinaryHeapBase {
            _kind: PhantomData,
            data: VecBase::default(),
        }
    }
}

impl<T, K, U: Uxx, const N: usize> Clone for BinaryHeapBase<T, K, U, N>
where
    K: Kind,
    T: Ord + Clone,
{
    fn clone(&self) -> Self {
        Self {
            _kind: self._kind,
            data: self.data.clone(),
        }
    }
}

impl<T, K, U: Uxx, const N: usize> Drop for BinaryHeapBase<T, K, U, N> {
    fn drop(&mut self) {
        unsafe { ptr::drop_in_place(self.data.as_mut_slice()) }
    }
}

impl<T, K, U: Uxx, const N: usize> fmt::Debug for BinaryHeapBase<T, K, U, N>
where
    K: Kind,
    T: Ord + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<'a, T, K, U: Uxx, const N: usize> IntoIterator for &'a BinaryHeapBase<T, K, U, N>
where
    K: Kind,
    T: Ord,
{
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use std::vec::Vec;

    use crate::binary_heap::{BinaryHeap, Max, Min};

    #[test]
    fn static_new() {
        static mut _B: BinaryHeap<i32, Min, 16> = BinaryHeap::new();
    }

    #[test]
    fn min() {
        let mut heap = BinaryHeap::<_, Min, 16>::new();
        heap.push(1).unwrap();
        heap.push(2).unwrap();
        heap.push(3).unwrap();
        heap.push(17).unwrap();
        heap.push(19).unwrap();
        heap.push(36).unwrap();
        heap.push(7).unwrap();
        heap.push(25).unwrap();
        heap.push(100).unwrap();

        assert_eq!(
            heap.iter().cloned().collect::<Vec<_>>(),
            [1, 2, 3, 17, 19, 36, 7, 25, 100]
        );

        assert_eq!(heap.pop(), Some(1));

        assert_eq!(
            heap.iter().cloned().collect::<Vec<_>>(),
            [2, 17, 3, 25, 19, 36, 7, 100]
        );

        assert_eq!(heap.pop(), Some(2));
        assert_eq!(heap.pop(), Some(3));
        assert_eq!(heap.pop(), Some(7));
        assert_eq!(heap.pop(), Some(17));
        assert_eq!(heap.pop(), Some(19));
        assert_eq!(heap.pop(), Some(25));
        assert_eq!(heap.pop(), Some(36));
        assert_eq!(heap.pop(), Some(100));
        assert_eq!(heap.pop(), None);

        assert!(heap.peek_mut().is_none());

        heap.push(1).unwrap();
        heap.push(2).unwrap();
        heap.push(10).unwrap();

        {
            let mut val = heap.peek_mut().unwrap();
            *val = 7;
        }

        assert_eq!(heap.pop(), Some(2));
        assert_eq!(heap.pop(), Some(7));
        assert_eq!(heap.pop(), Some(10));
        assert_eq!(heap.pop(), None);
    }

    #[test]
    fn max() {
        let mut heap = BinaryHeap::<_, Max, 16>::new();
        heap.push(1).unwrap();
        heap.push(2).unwrap();
        heap.push(3).unwrap();
        heap.push(17).unwrap();
        heap.push(19).unwrap();
        heap.push(36).unwrap();
        heap.push(7).unwrap();
        heap.push(25).unwrap();
        heap.push(100).unwrap();

        assert_eq!(
            heap.iter().cloned().collect::<Vec<_>>(),
            [100, 36, 19, 25, 3, 2, 7, 1, 17]
        );

        assert_eq!(heap.pop(), Some(100));

        assert_eq!(
            heap.iter().cloned().collect::<Vec<_>>(),
            [36, 25, 19, 17, 3, 2, 7, 1]
        );

        assert_eq!(heap.pop(), Some(36));
        assert_eq!(heap.pop(), Some(25));
        assert_eq!(heap.pop(), Some(19));
        assert_eq!(heap.pop(), Some(17));
        assert_eq!(heap.pop(), Some(7));
        assert_eq!(heap.pop(), Some(3));
        assert_eq!(heap.pop(), Some(2));
        assert_eq!(heap.pop(), Some(1));
        assert_eq!(heap.pop(), None);

        assert!(heap.peek_mut().is_none());

        heap.push(1).unwrap();
        heap.push(9).unwrap();
        heap.push(10).unwrap();

        {
            let mut val = heap.peek_mut().unwrap();
            *val = 7;
        }

        assert_eq!(heap.pop(), Some(9));
        assert_eq!(heap.pop(), Some(7));
        assert_eq!(heap.pop(), Some(1));
        assert_eq!(heap.pop(), None);
    }
}

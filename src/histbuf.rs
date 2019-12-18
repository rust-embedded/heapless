use generic_array::{ArrayLength, GenericArray, sequence::GenericSequence};
use as_slice::{AsSlice, AsMutSlice};

/// A "history buffer", similar to a write-only ring buffer.
///
/// This buffer keeps a fixed number of elements.  On push, the oldest element
/// is overwritten. It is useful to keep a history of values with some desired
/// depth, and for example calculate a rolling average.
///
/// The buffer is always fully initialized; depending on the constructor, the
/// initial value is either the default value for the element type or a supplied
/// initial value. This simplifies the API and is mostly irrelevant for the
/// intended use case.
///
/// # Examples
/// ```
/// use heapless::HistoryBuffer;
/// use heapless::consts::*;
///
/// // Initialize a new buffer with 8 elements, all initially zero.
/// let mut buf = HistoryBuffer::<_, U8>::new();
///
/// buf.push(3);
/// buf.push(5);
/// buf.extend(&[4, 4]);
///
/// // The first (oldest) element is still zero.
/// assert_eq!(buf.first(), &0);
/// // The last (newest) element is a four.
/// assert_eq!(buf.last(), &4);
/// for el in buf.iter() { println!("{:?}", el); }
///
/// // Now we can prepare an average of all values, which comes out to 2.
/// let avg = buf.iter().sum::<usize>() / buf.len();
/// assert_eq!(avg, 2);
/// ```
#[derive(Clone)]
pub struct HistoryBuffer<T, N>
where
    N: ArrayLength<T>,
{
    data: GenericArray<T, N>,
    write_at: usize,
}


impl<T, N> HistoryBuffer<T, N>
where
    N: ArrayLength<T>,
    T: Default,
{
    /// Constructs a new history buffer, where every element is filled with the
    /// default value of the type `T`.
    ///
    /// `HistoryBuffer` currently cannot be constructed in `const` context.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::HistoryBuffer;
    /// use heapless::consts::*;
    ///
    /// // Allocate a 16-element buffer on the stack
    /// let mut x: HistoryBuffer<u8, U16> = HistoryBuffer::new();
    /// // All elements are zero
    /// assert!(x.iter().eq([0; 16].iter()));
    /// ```
    pub fn new() -> Self {
        Self {
            data: Default::default(),
            write_at: 0,
        }
    }

    /// Clears the buffer, replacing every element with the default value of
    /// type `T`.
    pub fn clear(&mut self) {
        *self = Self::new();
    }
}

impl<T, N> HistoryBuffer<T, N>
where
    N: ArrayLength<T>,
    T: Clone,
{
    /// Constructs a new history buffer, where every element is the given value.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::HistoryBuffer;
    /// use heapless::consts::*;
    ///
    /// // Allocate a 16-element buffer on the stack
    /// let mut x: HistoryBuffer<u8, U16> = HistoryBuffer::new_with(4);
    /// // All elements are four
    /// assert!(x.iter().eq([4; 16].iter()));
    /// ```
    pub fn new_with(t: T) -> Self {
        Self {
            data: GenericArray::generate(|_| t.clone()),
            write_at: 0,
        }
    }

    /// Clears the buffer, replacing every element with the given value.
    pub fn clear_with(&mut self, t: T) {
        *self = Self::new_with(t);
    }
}

impl<T, N> HistoryBuffer<T, N>
where
    N: ArrayLength<T>,
{
    /// Returns the length of the buffer, which is the length of the underlying
    /// backing array.
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Writes an element to the buffer, overwriting the oldest value.
    pub fn push(&mut self, t: T) {
        self.data[self.write_at] = t;
        self.write_at = (self.write_at + 1) % self.len();
    }

    /// Clones and pushes all elements in a slice to the buffer.
    ///
    /// If the slice is longer than the buffer, only the last `self.len()`
    /// elements will actually be stored.
    pub fn extend_from_slice(&mut self, other: &[T])
    where
        T: Clone,
    {
        for item in other {
            self.push(item.clone());
        }
    }

    /// Returns a reference to the oldest (least recently pushed) value.
    pub fn first(&self) -> &T {
        &self.data[self.write_at]
    }

    /// Returns a reference to the newest (most recently pushed) value.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::HistoryBuffer;
    /// use heapless::consts::*;
    ///
    /// let mut x: HistoryBuffer<u8, U16> = HistoryBuffer::new();
    /// x.push(4);
    /// x.push(10);
    /// assert_eq!(x.last(), &10);
    /// ```
    pub fn last(&self) -> &T {
        &self.data[(self.write_at + self.len() - 1) % self.len()]
    }

    /// Returns an iterator over the elements of the buffer.
    ///
    /// Note: if the order of elements is not important, use
    /// `.as_slice().iter()` instead.
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            data: &self.data,
            cur: self.write_at,
            left: self.len(),
        }
    }

    /// Returns an iterator over mutable elements of the buffer.
    ///
    /// Note: if the order of elements is not important, use
    /// `.as_mut_slice().iter_mut()` instead.
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &'_ mut T> {
        let (p1, p2) = self.data.split_at_mut(self.write_at);
        p2.iter_mut().chain(p1)
    }
}

pub struct Iter<'a, T> {
    data: &'a [T],
    cur: usize,
    left: usize,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        if self.left == 0 {
            None
        } else {
            let el = &self.data[self.cur];
            self.cur = (self.cur + 1) % self.data.len();
            self.left -= 1;
            Some(el)
        }
    }
}

impl<T, N> Extend<T> for HistoryBuffer<T, N>
where
    N: ArrayLength<T>,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        for item in iter.into_iter() {
            self.push(item);
        }
    }
}

impl<'a, T, N> Extend<&'a T> for HistoryBuffer<T, N>
where
    T: 'a + Clone,
    N: ArrayLength<T>,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = &'a T>,
    {
        self.extend(iter.into_iter().cloned())
    }
}

impl<T, N> AsSlice for HistoryBuffer<T, N>
where
    N: ArrayLength<T>,
{
    type Element = T;

    /// Returns the array slice backing the buffer, without keeping track
    /// of the write position. Therefore, the element order is unspecified.
    fn as_slice(&self) -> &[T] {
        &self.data
    }
}

impl<T, N> AsMutSlice for HistoryBuffer<T, N>
where
    N: ArrayLength<T>,
{
    /// Returns the array slice backing the buffer, without keeping track
    /// of the write position. Therefore, the element order is unspecified.
    fn as_mut_slice(&mut self) -> &mut [T] {
        &mut self.data
    }
}

#[cfg(test)]
mod tests {
    use crate::{consts::*, HistoryBuffer};
    use as_slice::{AsSlice, AsMutSlice};

    #[test]
    fn new() {
        let x: HistoryBuffer<u8, U4> = HistoryBuffer::new_with(1);
        assert!(x.iter().eq([1; 4].iter()));

        let x: HistoryBuffer<u8, U4> = HistoryBuffer::new();
        assert!(x.iter().eq([0; 4].iter()));
    }

    #[test]
    fn push_iter() {
        let mut x: HistoryBuffer<u8, U4> = HistoryBuffer::new();
        x.push(1);
        x.push(4);
        assert!(x.iter().eq([0, 0, 1, 4].iter()));

        x.push(5);
        x.push(6);
        x.push(10);
        assert!(x.iter().eq([4, 5, 6, 10].iter()));

        x.extend([11, 12].iter());
        assert!(x.iter().eq([6, 10, 11, 12].iter()));

        assert!(x.iter_mut().eq([6, 10, 11, 12].iter()));
    }

    #[test]
    fn clear() {
        let mut x: HistoryBuffer<u8, U4> = HistoryBuffer::new_with(1);
        x.clear();
        assert!(x.iter().eq([0; 4].iter()));

        let mut x: HistoryBuffer<u8, U4> = HistoryBuffer::new();
        x.clear_with(1);
        assert!(x.iter().eq([1; 4].iter()));
    }

    #[test]
    fn first_last() {
        let mut x: HistoryBuffer<u8, U4> = HistoryBuffer::new();
        x.push(1);
        x.push(4);
        assert_eq!(x.first(), &0);
        assert_eq!(x.last(), &4);

        x.push(5);
        x.push(6);
        x.push(10);
        assert_eq!(x.first(), &4);
        assert_eq!(x.last(), &10);
    }

    #[test]
    fn as_slice() {
        let mut x: HistoryBuffer<u8, U4> = HistoryBuffer::new();

        x.extend([1, 2, 3, 4, 5].iter());

        assert_eq!(x.as_slice(), &[5, 2, 3, 4]);
        assert_eq!(x.as_mut_slice(), &mut [5, 2, 3, 4]);
    }
}

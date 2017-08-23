
#![deny(missing_docs)]
#![deny(warnings)]

use core::marker::PhantomData;

/// A circular buffer
pub struct CircularBuffer<T, A>
where
    A: AsMut<[T]> + AsRef<[T]>,
    T: Copy,
{
    _marker: PhantomData<[T]>,
    array: A,
    index: usize,
    len: usize,
}

impl<T, A> CircularBuffer<T, A>
where
    A: AsMut<[T]> + AsRef<[T]>,
    T: Copy,
{
    /// Creates a new empty circular buffer using `array` as backup storage.
    ///
    /// # Example
    /// ```
    /// #![feature(const_fn)]
    /// use heapless::CircularBuffer;
    /// const LEN: usize = 16;
    /// // with let
    /// let buf_let = CircularBuffer::new([0;LEN]);
    /// // with const
    /// const BUF_CONST: CircularBuffer<u8, [u8; LEN]>
    ///     = CircularBuffer::new([0;LEN]);
    /// // with static
    /// static BUF_STATIC: CircularBuffer<u8, [u8; LEN]>
    ///     = CircularBuffer::new([0;LEN]);
    /// // with slice
    /// let mut array = [0_usize; 8];
    /// let mut buf_slice = CircularBuffer::new(&mut array);
    /// ```
    #[inline]
    pub const fn new(array: A) -> Self {
        CircularBuffer {
            _marker: PhantomData,
            array: array,
            index: 0,
            len: 0,
        }
    }

    /// Creates a new circular buffer using `array` as backup storage.
    /// Keeps the values and the length of the array.
    /// The backup storage is completly used upon creation.
    /// Insertions will overwrite at the start of the array.
    ///
    /// # Example
    /// ```
    /// use heapless::CircularBuffer;
    /// let buf = CircularBuffer::from_array([1,2,3]);
    /// assert!(buf.is_full());
    /// ```
    #[inline]
    pub fn from_array(array: A) -> Self {
        let len = array.as_ref().len();
        CircularBuffer {
            _marker: PhantomData,
            array: array,
            index: 0,
            len: len,
        }
    }

    /// Returns the capacity of this buffer.
    ///
    ///
    /// # Example
    /// ```
    /// use heapless::CircularBuffer;
    /// const LEN: usize = 16;
    /// let buf = CircularBuffer::new([0;LEN]);
    /// assert_eq!(buf.capacity(), LEN);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        self.array.as_ref().len()
    }

    /// Returns the current length of this buffer.
    ///
    /// # Example
    /// ```
    /// use heapless::CircularBuffer;
    /// let buf = CircularBuffer::from_array([1,2,3]);
    /// assert_eq!(buf.len(), 3);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns the current index of this buffer.
    /// This is the next place to push to.
    ///
    /// # Example
    /// ```
    /// use heapless::CircularBuffer;
    /// let buf = CircularBuffer::from_array([1,2,3]);
    /// assert_eq!(buf.index(), 0);
    /// ```
    #[inline]
    pub fn index(&self) -> usize {
        self.index
    }

    /// Returns the fist adressable index in the buffer.
    #[inline]
    pub fn first_index(&self) -> usize {
        let index = self.index() as isize;
        let len = self.len() as isize;
        let capacity = self.capacity() as isize;
        ((index - len + capacity) % capacity) as usize
    }

    /// Returns `true` if the buffer is empty.
    ///
    /// # Example
    /// ```
    /// use heapless::CircularBuffer;
    /// let buf = CircularBuffer::new([0;8]);
    /// assert!(buf.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns `true` if the buffer is saturated.
    ///
    /// Note that elements can still be inserted but will overwrite
    /// the last ones.
    ///
    /// # Example
    /// ```
    /// use heapless::CircularBuffer;
    /// let buf = CircularBuffer::from_array([1,2,3]);
    /// assert!(buf.is_full());
    /// ```
    #[inline]
    pub fn is_full(&self) -> bool {
        self.len() == self.capacity()
    }

    /// Pushes `element` into the buffer.
    ///
    /// This will overwrite an old value if the buffer is full.
    /// # Example
    /// ```
    /// use heapless::CircularBuffer;
    /// let mut buf = CircularBuffer::new([0; 2]);
    /// buf.push(1);
    /// buf.push(2);
    /// buf.push(3);
    /// assert_eq!(buf.pop(), Some(3));
    /// assert_eq!(buf.pop(), Some(2));
    /// assert_eq!(buf.pop(), None);
    /// ```
    #[inline]
    pub fn push(&mut self, element: T) {
        let len = self.len();
        let capacity = self.capacity();
        let index = self.index();
        if len < capacity {
            unsafe {
                self.set_len(len + 1);
            }
        }
        {
            let slice = self.array.as_mut();
            slice[index] = element;
        }
        unsafe {
            self.set_index((index + 1) as isize);
        }
    }

    /// Pops the most recently inserted element.
    ///
    /// Returns `None` if the buffer is empty.
    ///
    /// # Example
    /// ```
    /// use heapless::CircularBuffer;
    /// let mut buf = CircularBuffer::from_array([1,2]);
    /// assert_eq!(buf.pop(), Some(2));
    /// assert_eq!(buf.pop(), Some(1));
    /// assert_eq!(buf.pop(), None);
    /// ```
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }
        let len = self.len();
        let index = self.index() as isize;
        unsafe {
            self.set_len(len - 1);
            self.set_index(index - 1);
            Some(self.array.as_ref()[self.index()])
        }
    }

    /// Returns an iterator over the elements as `&T`
    #[inline]
    pub fn iter(&self) -> Iter<T, A> {
        Iter::new(&self)
    }

    /// Sets the length of the buffer.
    ///
    /// This is unsafe because no checks are performed, memory can be leaked
    /// or uninitialized memory may be exposed.
    #[inline]
    unsafe fn set_len(&mut self, len: usize) {
        self.len = len;
    }

    /// Sets the index of the buffer with wrap-around.
    /// This is the next place to insert to.
    ///
    /// This is unsafe because memory can be leaked
    /// or uninitialized memory may be exposed.
    #[inline]
    unsafe fn set_index(&mut self, index: isize) {
        let capactity = self.capacity() as isize;
        self.index = ((capactity + index) % capactity) as usize;
    }
}

/// Iterator for Circular buffer
pub struct Iter<'a, T, A>
where
    A: 'a + AsMut<[T]> + AsRef<[T]>,
    T: 'a + Copy,
{
    buffer: &'a CircularBuffer<T, A>,
    next_index: Option<usize>,
}

impl<'a, T, A> Iter<'a, T, A>
where
    A: 'a + AsMut<[T]> + AsRef<[T]>,
    T: 'a + Copy,
{
    /// Creates a new iterator with a buffer
    #[inline]
    pub fn new(buf: &'a CircularBuffer<T, A>) -> Self {
        Iter {
            buffer: buf,
            next_index: if buf.is_empty() {
                None
            } else {
                Some(buf.first_index())
            },
        }
    }
}

impl<'a, T, A> Iterator for Iter<'a, T, A>
where
    A: 'a + AsMut<[T]> + AsRef<[T]>,
    T: 'a + Copy,
{
    type Item = &'a T;
    #[inline]
    fn next(&mut self) -> Option<&'a T> {
        let next = self.next_index;
        match next {
            Some(index) => {
                let buf_index = (self.buffer.index() + self.buffer.capacity() - 1)
                    % self.buffer.capacity();
                self.next_index = if index == buf_index {
                    None
                } else {
                    Some((index + 1) % self.buffer.capacity())
                };
                Some(&self.buffer.array.as_ref()[index])
            }
            None => None,
        }
    }
}

#[cfg(test)]
mod test {
    use super::CircularBuffer;
    #[test]
    fn iter() {
        let mut buf = CircularBuffer::new([0; 4]);
        buf.push(1);
        buf.push(2);
        buf.push(3);
        buf.push(4);
        buf.push(5);
        let _ = buf.pop();
        let mut iter = buf.iter();
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), Some(&4));
        assert_eq!(iter.next(), None);
    }
}

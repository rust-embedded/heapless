use core::{
    cmp::Ordering,
    fmt, hash,
    iter::FromIterator,
    mem,
    mem::{ManuallyDrop, MaybeUninit},
    ops, ptr, slice,
};

#[repr(C)]
struct VecBuf<T, const N: usize, A> {
    alignment_field: [A; 0],
    buffer: [MaybeUninit<T>; N],
}

/// A fixed capacity [`Vec`](https://doc.rust-lang.org/std/vec/struct.Vec.html).
///
/// # Examples
///
/// ```
/// use heapless::Vec;
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
pub struct Vec<T, const N: usize, A = u8> {
    // NOTE order is important for optimizations. the `len` first layout lets the compiler optimize
    // `new` to: reserve stack space and zero the first word. With the fields in the reverse order
    // the compiler optimizes `new` to `memclr`-ing the *entire* stack space, including the `buffer`
    // field which should be left uninitialized. Optimizations were last checked with Rust 1.60
    len: usize,

    storage: VecBuf<T, N, A>,
}

impl<T, const N: usize, A> VecBuf<T, N, A> {
    const ELEM: MaybeUninit<T> = MaybeUninit::uninit();
    const INIT: [MaybeUninit<T>; N] = [Self::ELEM; N]; // important for optimization of `new`

    const fn new() -> Self {
        Self {
            alignment_field: [],
            buffer: Self::INIT,
        }
    }

    const fn as_ptr(&self) -> *const T {
        self.buffer.as_ptr() as *const T
    }

    fn as_mut_ptr(&mut self) -> *mut T {
        self.buffer.as_mut_ptr() as *mut T
    }

    unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut MaybeUninit<T> {
        self.buffer.get_unchecked_mut(index)
    }
}

impl<T, const N: usize, A> Vec<T, N, A> {
    /// Constructs a new, empty vector with a fixed capacity of `N`
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::Vec;
    ///
    /// // allocate the vector on the stack
    /// let mut x: Vec<u8, 16> = Vec::new();
    ///
    /// // allocate the vector in a static variable
    /// static mut X: Vec<u8, 16> = Vec::new();
    /// ```
    /// `Vec` `const` constructor; wrap the returned value in [`Vec`].
    pub const fn new() -> Self {
        Self {
            len: 0,
            storage: VecBuf::new(),
        }
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
    #[allow(clippy::result_unit_err)]
    pub fn from_slice(other: &[T]) -> Result<Self, ()>
    where
        T: Clone,
    {
        let mut v = Vec::new();
        v.extend_from_slice(other)?;
        Ok(v)
    }

    /// Constructs a new vector with a fixed capacity of `N`, initializing
    /// it with the provided array.
    ///
    /// The length of the provided array, `M` may be equal to _or_ less than
    /// the capacity of the vector, `N`.
    ///
    /// If the length of the provided array is greater than the capacity of the
    /// vector a compile-time error will be produced.
    pub fn from_array<const M: usize>(src: [T; M]) -> Self {
        // Const assert M >= 0
        crate::sealed::greater_than_eq_0::<M>();
        // Const assert N >= M
        crate::sealed::greater_than_eq::<N, M>();

        // We've got to copy `src`, but we're functionally moving it. Don't run
        // any Drop code for T.
        let src = ManuallyDrop::new(src);

        if N == M {
            Self {
                len: N,
                // NOTE(unsafe) ManuallyDrop<[T; M]> and [MaybeUninit<T>; N]
                // have the same layout when N == M.
                buffer: unsafe { mem::transmute_copy(&src) },
            }
        } else {
            let mut v = Vec::<T, N>::new();

            for (src_elem, dst_elem) in src.iter().zip(v.buffer.iter_mut()) {
                // NOTE(unsafe) src element is not going to drop as src itself
                // is wrapped in a ManuallyDrop.
                dst_elem.write(unsafe { ptr::read(src_elem) });
            }

            v.len = M;
            v
        }
    }

    /// Clones a vec into a new vec
    pub(crate) fn clone(&self) -> Self
    where
        T: Clone,
    {
        let mut new = Self::new();
        // avoid `extend_from_slice` as that introduces a runtime check/panicking branch
        for elem in self {
            unsafe {
                new.push_unchecked(elem.clone());
            }
        }
        new
    }

    /// Returns a raw pointer to the vector’s buffer.
    pub fn as_ptr(&self) -> *const T {
        self.storage.as_ptr()
    }

    /// Returns a raw pointer to the vector’s buffer, which may be mutated through.
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.storage.as_mut_ptr()
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
        unsafe { slice::from_raw_parts(self.storage.as_ptr(), self.len) }
    }

    /// Returns the contents of the vector as an array of length `M` if the length
    /// of the vector is exactly `M`, otherwise returns `Err(self)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::Vec;
    /// let buffer: Vec<u8, 42> = Vec::from_slice(&[1, 2, 3, 5, 8]).unwrap();
    /// let array: [u8; 5] = buffer.into_array().unwrap();
    /// assert_eq!(array, [1, 2, 3, 5, 8]);
    /// ```
    pub fn into_array<const M: usize>(self) -> Result<[T; M], Self> {
        if self.len() == M {
            // This is how the unstable `MaybeUninit::array_assume_init` method does it
            let array = unsafe { (self.as_ptr() as *const [T; M]).read() };

            // We don't want `self`'s destructor to be called because that would drop all the
            // items in the array
            core::mem::forget(self);

            Ok(array)
        } else {
            Err(self)
        }
    }

    /// Extracts a mutable slice containing the entire vector.
    ///
    /// Equivalent to `&mut s[..]`.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::Vec;
    /// let mut buffer: Vec<u8, 5> = Vec::from_slice(&[1, 2, 3, 5, 8]).unwrap();
    /// buffer[0] = 9;
    /// assert_eq!(buffer.as_slice(), &[9, 2, 3, 5, 8]);
    /// ```
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        // NOTE(unsafe) avoid bound checks in the slicing operation
        // &mut buffer[..self.len]
        unsafe { slice::from_raw_parts_mut(self.as_mut_ptr(), self.len) }
    }

    /// Returns the maximum number of elements the vector can hold.
    pub const fn capacity(&self) -> usize {
        N
    }

    /// Clears the vector, removing all values.
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
    #[allow(clippy::result_unit_err)]
    pub fn extend_from_slice(&mut self, other: &[T]) -> Result<(), ()>
    where
        T: Clone,
    {
        if self.len + other.len() > self.capacity() {
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
        if self.len != 0 {
            Some(unsafe { self.pop_unchecked() })
        } else {
            None
        }
    }

    /// Appends an `item` to the back of the collection
    ///
    /// Returns back the `item` if the vector is full
    pub fn push(&mut self, item: T) -> Result<(), T> {
        if self.len < self.capacity() {
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
    pub unsafe fn pop_unchecked(&mut self) -> T {
        debug_assert!(!self.is_empty());

        self.len -= 1;
        self.storage.get_unchecked_mut(self.len).as_ptr().read()
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

        *self.storage.get_unchecked_mut(self.len) = MaybeUninit::new(item);

        self.len += 1;
    }

    /// Shortens the vector, keeping the first `len` elements and dropping the rest.
    pub fn truncate(&mut self, len: usize) {
        // This is safe because:
        //
        // * the slice passed to `drop_in_place` is valid; the `len > self.len`
        //   case avoids creating an invalid slice, and
        // * the `len` of the vector is shrunk before calling `drop_in_place`,
        //   such that no value will be dropped twice in case `drop_in_place`
        //   were to panic once (if it panics twice, the program aborts).
        unsafe {
            // Note: It's intentional that this is `>` and not `>=`.
            //       Changing it to `>=` has negative performance
            //       implications in some cases. See rust-lang/rust#78884 for more.
            if len > self.len {
                return;
            }
            let remaining_len = self.len - len;
            let s = ptr::slice_from_raw_parts_mut(self.as_mut_ptr().add(len), remaining_len);
            self.len = len;
            ptr::drop_in_place(s);
        }
    }

    /// Resizes the Vec in-place so that len is equal to new_len.
    ///
    /// If new_len is greater than len, the Vec is extended by the
    /// difference, with each additional slot filled with value. If
    /// new_len is less than len, the Vec is simply truncated.
    ///
    /// See also [`resize_default`](Self::resize_default).
    #[allow(clippy::result_unit_err)]
    pub fn resize(&mut self, new_len: usize, value: T) -> Result<(), ()>
    where
        T: Clone,
    {
        if new_len > self.capacity() {
            return Err(());
        }

        if new_len > self.len {
            while self.len < new_len {
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
    /// difference, with each additional slot filled with `Default::default()`.
    /// If `new_len` is less than `len`, the `Vec` is simply truncated.
    ///
    /// See also [`resize`](Self::resize).
    #[allow(clippy::result_unit_err)]
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
    /// [`truncate`]: Self::truncate
    /// [`resize`]: Self::resize
    /// [`extend`]: core::iter::Extend
    /// [`clear`]: Self::clear
    ///
    /// # Safety
    ///
    /// - `new_len` must be less than or equal to [`capacity()`].
    /// - The elements at `old_len..new_len` must be initialized.
    ///
    /// [`capacity()`]: Self::capacity
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
    ///     .cloned(),
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
        debug_assert!(new_len <= self.capacity());

        self.len = new_len
    }

    /// Removes an element from the vector and returns it.
    ///
    /// The removed element is replaced by the last element of the vector.
    ///
    /// This does not preserve ordering, but is *O*(1).
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
        assert!(index < self.len);
        unsafe { self.swap_remove_unchecked(index) }
    }

    /// Removes an element from the vector and returns it.
    ///
    /// The removed element is replaced by the last element of the vector.
    ///
    /// This does not preserve ordering, but is *O*(1).
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
        let value = ptr::read(self.as_ptr().add(index));
        let base_ptr = self.as_mut_ptr();
        ptr::copy(base_ptr.add(length - 1), base_ptr.add(index), 1);
        self.len -= 1;
        value
    }

    /// Returns true if the vec is full
    #[inline]
    pub fn is_full(&self) -> bool {
        self.len == self.capacity()
    }

    /// Returns true if the vec is empty
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
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
        self.len >= n && needle == &self[..n]
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

    /// Inserts an element at position `index` within the vector, shifting all
    /// elements after it to the right.
    ///
    /// Returns back the `element` if the vector is full.
    ///
    /// # Panics
    ///
    /// Panics if `index > len`.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::Vec;
    ///
    /// let mut vec: Vec<_, 8> = Vec::from_slice(&[1, 2, 3]).unwrap();
    /// vec.insert(1, 4);
    /// assert_eq!(vec, [1, 4, 2, 3]);
    /// vec.insert(4, 5);
    /// assert_eq!(vec, [1, 4, 2, 3, 5]);
    /// ```
    pub fn insert(&mut self, index: usize, element: T) -> Result<(), T> {
        let len = self.len();
        if index > len {
            panic!(
                "insertion index (is {}) should be <= len (is {})",
                index, len
            );
        }

        // check there's space for the new element
        if self.is_full() {
            return Err(element);
        }

        unsafe {
            // infallible
            // The spot to put the new value
            {
                let p = self.as_mut_ptr().add(index);
                // Shift everything over to make space. (Duplicating the
                // `index`th element into two consecutive places.)
                ptr::copy(p, p.offset(1), len - index);
                // Write it in, overwriting the first copy of the `index`th
                // element.
                ptr::write(p, element);
            }
            self.set_len(len + 1);
        }

        Ok(())
    }

    /// Removes and returns the element at position `index` within the vector,
    /// shifting all elements after it to the left.
    ///
    /// Note: Because this shifts over the remaining elements, it has a
    /// worst-case performance of *O*(n). If you don't need the order of
    /// elements to be preserved, use [`swap_remove`] instead. If you'd like to
    /// remove elements from the beginning of the `Vec`, consider using
    /// [`Deque::pop_front`] instead.
    ///
    /// [`swap_remove`]: Vec::swap_remove
    /// [`Deque::pop_front`]: crate::Deque::pop_front
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::Vec;
    ///
    /// let mut v: Vec<_, 8> = Vec::from_slice(&[1, 2, 3]).unwrap();
    /// assert_eq!(v.remove(1), 2);
    /// assert_eq!(v, [1, 3]);
    /// ```
    pub fn remove(&mut self, index: usize) -> T {
        let len = self.len();
        if index >= len {
            panic!("removal index (is {}) should be < len (is {})", index, len);
        }
        unsafe {
            // infallible
            let ret;
            {
                // the place we are taking from.
                let ptr = self.as_mut_ptr().add(index);
                // copy it out, unsafely having a copy of the value on
                // the stack and in the vector at the same time.
                ret = ptr::read(ptr);

                // Shift everything down to fill in that spot.
                ptr::copy(ptr.offset(1), ptr, len - index - 1);
            }
            self.set_len(len - 1);
            ret
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` for which `f(&e)` returns `false`.
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::Vec;
    ///
    /// let mut vec: Vec<_, 8> = Vec::from_slice(&[1, 2, 3, 4]).unwrap();
    /// vec.retain(|&x| x % 2 == 0);
    /// assert_eq!(vec, [2, 4]);
    /// ```
    ///
    /// Because the elements are visited exactly once in the original order,
    /// external state may be used to decide which elements to keep.
    ///
    /// ```
    /// use heapless::Vec;
    ///
    /// let mut vec: Vec<_, 8> = Vec::from_slice(&[1, 2, 3, 4, 5]).unwrap();
    /// let keep = [false, true, true, false, true];
    /// let mut iter = keep.iter();
    /// vec.retain(|_| *iter.next().unwrap());
    /// assert_eq!(vec, [2, 3, 5]);
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.retain_mut(|elem| f(elem));
    }

    /// Retains only the elements specified by the predicate, passing a mutable reference to it.
    ///
    /// In other words, remove all elements `e` such that `f(&mut e)` returns `false`.
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::Vec;
    ///
    /// let mut vec: Vec<_, 8> = Vec::from_slice(&[1, 2, 3, 4]).unwrap();
    /// vec.retain_mut(|x| {
    ///     if *x <= 3 {
    ///         *x += 1;
    ///         true
    ///     } else {
    ///         false
    ///     }
    /// });
    /// assert_eq!(vec, [2, 3, 4]);
    /// ```
    pub fn retain_mut<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T) -> bool,
    {
        let original_len = self.len();
        // Avoid double drop if the drop guard is not executed,
        // since we may make some holes during the process.
        unsafe { self.set_len(0) };

        // Vec: [Kept, Kept, Hole, Hole, Hole, Hole, Unchecked, Unchecked]
        //      |<-              processed len   ->| ^- next to check
        //                  |<-  deleted cnt     ->|
        //      |<-              original_len                          ->|
        // Kept: Elements which predicate returns true on.
        // Hole: Moved or dropped element slot.
        // Unchecked: Unchecked valid elements.
        //
        // This drop guard will be invoked when predicate or `drop` of element panicked.
        // It shifts unchecked elements to cover holes and `set_len` to the correct length.
        // In cases when predicate and `drop` never panick, it will be optimized out.
        struct BackshiftOnDrop<'a, T, const N: usize, A> {
            v: &'a mut Vec<T, N, A>,
            processed_len: usize,
            deleted_cnt: usize,
            original_len: usize,
        }

        impl<T, const N: usize, A> Drop for BackshiftOnDrop<'_, T, N, A> {
            fn drop(&mut self) {
                if self.deleted_cnt > 0 {
                    // SAFETY: Trailing unchecked items must be valid since we never touch them.
                    unsafe {
                        ptr::copy(
                            self.v.as_ptr().add(self.processed_len),
                            self.v
                                .as_mut_ptr()
                                .add(self.processed_len - self.deleted_cnt),
                            self.original_len - self.processed_len,
                        );
                    }
                }
                // SAFETY: After filling holes, all items are in contiguous memory.
                unsafe {
                    self.v.set_len(self.original_len - self.deleted_cnt);
                }
            }
        }

        let mut g = BackshiftOnDrop {
            v: self,
            processed_len: 0,
            deleted_cnt: 0,
            original_len,
        };

        fn process_loop<F, T, const N: usize, A, const DELETED: bool>(
            original_len: usize,
            f: &mut F,
            g: &mut BackshiftOnDrop<'_, T, N, A>,
        ) where
            F: FnMut(&mut T) -> bool,
        {
            while g.processed_len != original_len {
                let p = g.v.as_mut_ptr();
                // SAFETY: Unchecked element must be valid.
                let cur = unsafe { &mut *p.add(g.processed_len) };
                if !f(cur) {
                    // Advance early to avoid double drop if `drop_in_place` panicked.
                    g.processed_len += 1;
                    g.deleted_cnt += 1;
                    // SAFETY: We never touch this element again after dropped.
                    unsafe { ptr::drop_in_place(cur) };
                    // We already advanced the counter.
                    if DELETED {
                        continue;
                    } else {
                        break;
                    }
                }
                if DELETED {
                    // SAFETY: `deleted_cnt` > 0, so the hole slot must not overlap with current element.
                    // We use copy for move, and never touch this element again.
                    unsafe {
                        let hole_slot = p.add(g.processed_len - g.deleted_cnt);
                        ptr::copy_nonoverlapping(cur, hole_slot, 1);
                    }
                }
                g.processed_len += 1;
            }
        }

        // Stage 1: Nothing was deleted.
        process_loop::<F, T, N, A, false>(original_len, &mut f, &mut g);

        // Stage 2: Some elements were deleted.
        process_loop::<F, T, N, A, true>(original_len, &mut f, &mut g);

        // All item are processed. This can be optimized to `set_len` by LLVM.
        drop(g);
    }
}

impl<const N: usize, A> Vec<u8, N, A> {
    /// Transmutes the filled buffer to the output type. The storage of the length of the [`Vec`] does
    /// not participate in the transmutation.
    ///
    /// # Safety
    ///
    /// - The buffer must be full.
    /// - The size of the output type must be equal to the size of the **buffer** (rather than [`Vec`]).
    /// - The alignment of the `Vec` must be equal or be a multiple of the alignment of the output.
    ///
    /// # Panics
    ///
    /// In debug mode, this method panics...
    ///
    /// - If the buffer isn't full.
    /// - If the size of the output type doesn't match the size of the buffer.
    /// - If the alignment of the `Vec` isn't equal or a multiple of the alignment of the output.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::Vec;
    ///
    /// let mut v: Vec<u8, 2, u16> = Vec::new();
    /// v.extend_from_slice(&[0, 0]).unwrap();
    /// let number: u16 = unsafe { v.transmute_buffer() };
    /// assert_eq!(number, 0u16);
    /// ```
    pub unsafe fn transmute_buffer<O: Sized>(self) -> O {
        // While transmuting to the smaller type is not UB,
        // it's discouraged.
        #[cfg(debug_assertions)]
        if self.len() != N {
            panic!("Vec::transmute_buffer: the buffer isn't full");
        };
        #[cfg(debug_assertions)]
        if N * core::mem::size_of::<u8>() != core::mem::size_of::<O>() {
            panic!("Vec::transmute_buffer: size mismatch");
        };
        #[cfg(debug_assertions)]
        if core::mem::align_of::<A>() % core::mem::align_of::<O>() != 0 {
            panic!("Vec::transmute_buffer: alignment mismatch");
        };
        // transmute wouldn't work because the size of O is unknown
        // transmute_unchecked is unstable
        core::mem::transmute_copy(&self.storage.buffer)
    }
}

// Trait implementations

impl<T, const N: usize, A> Default for Vec<T, N, A> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const N: usize, A> fmt::Debug for Vec<T, N, A>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <[T] as fmt::Debug>::fmt(self, f)
    }
}

impl<const N: usize> fmt::Write for Vec<u8, N> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        match self.extend_from_slice(s.as_bytes()) {
            Ok(()) => Ok(()),
            Err(_) => Err(fmt::Error),
        }
    }
}

impl<T, const N: usize, A> Drop for Vec<T, N, A> {
    fn drop(&mut self) {
        // We drop each element used in the vector by turning into a `&mut [T]`.
        unsafe {
            ptr::drop_in_place(self.as_mut_slice());
        }
    }
}

impl<T, const N: usize, const M: usize, A> From<[T; M]> for Vec<T, N, A> {
    fn from(array: [T; M]) -> Self {
        Self::from_array(array)
    }
}

impl<'a, T: Clone, const N: usize, A> TryFrom<&'a [T]> for Vec<T, N, A> {
    type Error = ();

    fn try_from(slice: &'a [T]) -> Result<Self, Self::Error> {
        Vec::from_slice(slice)
    }
}

impl<T, const N: usize, A> Extend<T> for Vec<T, N, A> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        self.extend(iter)
    }
}

impl<'a, T, const N: usize, A> Extend<&'a T> for Vec<T, N, A>
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

impl<T, const N: usize, A> hash::Hash for Vec<T, N, A>
where
    T: core::hash::Hash,
{
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        <[T] as hash::Hash>::hash(self, state)
    }
}

impl<'a, T, const N: usize, A> IntoIterator for &'a Vec<T, N, A> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T, const N: usize, A> IntoIterator for &'a mut Vec<T, N, A> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T, const N: usize, A> FromIterator<T> for Vec<T, N, A> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let mut vec = Vec::new();
        for i in iter {
            vec.push(i).ok().expect("Vec::from_iter overflow");
        }
        vec
    }
}

/// An iterator that moves out of an [`Vec`][`Vec`].
///
/// This struct is created by calling the `into_iter` method on [`Vec`][`Vec`].
pub struct IntoIter<T, const N: usize, A> {
    vec: Vec<T, N, A>,
    next: usize,
}

impl<T, const N: usize, A> Iterator for IntoIter<T, N, A> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        if self.next < self.vec.len() {
            let item = unsafe {
                self.vec
                    .storage
                    .get_unchecked_mut(self.next)
                    .as_ptr()
                    .read()
            };
            self.next += 1;
            Some(item)
        } else {
            None
        }
    }
}

impl<T, const N: usize, A> Clone for IntoIter<T, N, A>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        let mut vec = Vec::new();

        if self.next < self.vec.len() {
            let s = unsafe {
                slice::from_raw_parts(
                    (self.vec.storage.as_ptr()).add(self.next),
                    self.vec.len() - self.next,
                )
            };
            vec.extend_from_slice(s).ok();
        }

        Self { vec, next: 0 }
    }
}

impl<T, const N: usize, A> Drop for IntoIter<T, N, A> {
    fn drop(&mut self) {
        unsafe {
            // Drop all the elements that have not been moved out of vec
            ptr::drop_in_place(&mut self.vec.as_mut_slice()[self.next..]);
            // Prevent dropping of other elements
            self.vec.len = 0;
        }
    }
}

impl<T, const N: usize, A> IntoIterator for Vec<T, N, A> {
    type Item = T;
    type IntoIter = IntoIter<T, N, A>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter { vec: self, next: 0 }
    }
}

impl<T1, T2, const N1: usize, const N2: usize, A1, A2> PartialEq<Vec<T2, N2, A2>>
    for Vec<T1, N1, A1>
where
    T1: PartialEq<T2>,
{
    fn eq(&self, other: &Vec<T2, N2, A2>) -> bool {
        <[T1]>::eq(self, &**other)
    }
}

// Vec<A, N> == [B]
impl<T1, T2, const N: usize, A> PartialEq<[T2]> for Vec<T1, N, A>
where
    T1: PartialEq<T2>,
{
    fn eq(&self, other: &[T2]) -> bool {
        <[T1]>::eq(self, other)
    }
}

// [B] == Vec<A, N>
impl<T1, T2, const N: usize, A> PartialEq<Vec<T1, N, A>> for [T2]
where
    T1: PartialEq<T2>,
{
    fn eq(&self, other: &Vec<T1, N, A>) -> bool {
        <[T1]>::eq(other, self)
    }
}

// Vec<A, N> == &[B]
impl<T1, T2, const N: usize, A> PartialEq<&[T2]> for Vec<T1, N, A>
where
    T1: PartialEq<T2>,
{
    fn eq(&self, other: &&[T2]) -> bool {
        <[T1]>::eq(self, &other[..])
    }
}

// &[B] == Vec<A, N>
impl<T1, T2, const N: usize, A> PartialEq<Vec<T1, N, A>> for &[T2]
where
    T1: PartialEq<T2>,
{
    fn eq(&self, other: &Vec<T1, N, A>) -> bool {
        <[T1]>::eq(other, &self[..])
    }
}

// Vec<A, N> == &mut [B]
impl<T1, T2, const N: usize, A> PartialEq<&mut [T2]> for Vec<T1, N, A>
where
    T1: PartialEq<T2>,
{
    fn eq(&self, other: &&mut [T2]) -> bool {
        <[T1]>::eq(self, &other[..])
    }
}

// &mut [B] == Vec<A, N>
impl<T1, T2, const N: usize, A> PartialEq<Vec<T1, N, A>> for &mut [T2]
where
    T1: PartialEq<T2>,
{
    fn eq(&self, other: &Vec<T1, N, A>) -> bool {
        <[T1]>::eq(other, &self[..])
    }
}

// Vec<A, N> == [B; M]
// Equality does not require equal capacity
impl<T1, T2, const N: usize, const M: usize, A> PartialEq<[T2; M]> for Vec<T1, N, A>
where
    T1: PartialEq<T2>,
{
    fn eq(&self, other: &[T2; M]) -> bool {
        <[T1]>::eq(self, &other[..])
    }
}

// [B; M] == Vec<A, N>
// Equality does not require equal capacity
impl<T1, T2, const N: usize, const M: usize, A> PartialEq<Vec<T1, N, A>> for [T2; M]
where
    T1: PartialEq<T2>,
{
    fn eq(&self, other: &Vec<T1, N, A>) -> bool {
        <[T1]>::eq(other, &self[..])
    }
}

// Vec<A, N> == &[B; M]
// Equality does not require equal capacity
impl<T1, T2, const N: usize, const M: usize, A> PartialEq<&[T2; M]> for Vec<T1, N, A>
where
    T1: PartialEq<T2>,
{
    fn eq(&self, other: &&[T2; M]) -> bool {
        <[T1]>::eq(self, &other[..])
    }
}

// &[B; M] == Vec<A, N>
// Equality does not require equal capacity
impl<T1, T2, const N: usize, const M: usize, A> PartialEq<Vec<T1, N, A>> for &[T2; M]
where
    T1: PartialEq<T2>,
{
    fn eq(&self, other: &Vec<T1, N, A>) -> bool {
        <[T1]>::eq(other, &self[..])
    }
}

// Implements Eq if underlying data is Eq
impl<T, const N: usize, A> Eq for Vec<T, N, A> where T: Eq {}

impl<T, const N1: usize, const N2: usize, A1, A2> PartialOrd<Vec<T, N2, A2>> for Vec<T, N1, A1>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &Vec<T, N2, A2>) -> Option<Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }
}

impl<T, const N: usize, A> Ord for Vec<T, N, A>
where
    T: Ord,
{
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        Ord::cmp(&**self, &**other)
    }
}

impl<T, const N: usize, A> ops::Deref for Vec<T, N, A> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, const N: usize, A> ops::DerefMut for Vec<T, N, A> {
    fn deref_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T, const N: usize, A> AsRef<Vec<T, N, A>> for Vec<T, N, A> {
    #[inline]
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<T, const N: usize, A> AsMut<Vec<T, N, A>> for Vec<T, N, A> {
    #[inline]
    fn as_mut(&mut self) -> &mut Self {
        self
    }
}

impl<T, const N: usize, A> AsRef<[T]> for Vec<T, N, A> {
    #[inline]
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T, const N: usize, A> AsMut<[T]> for Vec<T, N, A> {
    #[inline]
    fn as_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<T, const N: usize, A> Clone for Vec<T, N, A>
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
        let mut _v: Vec<i32, 4> = Vec::new();
    }

    #[test]
    fn is_full_empty() {
        let mut v: Vec<i32, 4> = Vec::new();

        assert!(v.is_empty());
        assert!(!v.is_full());

        v.push(1).unwrap();
        assert!(!v.is_empty());
        assert!(!v.is_full());

        v.push(1).unwrap();
        assert!(!v.is_empty());
        assert!(!v.is_full());

        v.push(1).unwrap();
        assert!(!v.is_empty());
        assert!(!v.is_full());

        v.push(1).unwrap();
        assert!(!v.is_empty());
        assert!(v.is_full());
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

        assert_eq!(Droppable::count(), 0);

        {
            let mut v: Vec<Droppable, 2> = Vec::new();
            v.push(Droppable::new()).ok().unwrap();
            v.push(Droppable::new()).ok().unwrap();
        }

        assert_eq!(Droppable::count(), 0);
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
    fn cmp() {
        let mut xs: Vec<i32, 4> = Vec::new();
        let mut ys: Vec<i32, 4> = Vec::new();

        assert_eq!(xs, ys);

        xs.push(1).unwrap();
        ys.push(2).unwrap();

        assert!(xs < ys);
    }

    #[test]
    fn cmp_heterogenous_size() {
        let mut xs: Vec<i32, 4> = Vec::new();
        let mut ys: Vec<i32, 8> = Vec::new();

        assert_eq!(xs, ys);

        xs.push(1).unwrap();
        ys.push(2).unwrap();

        assert!(xs < ys);
    }

    #[test]
    fn cmp_with_arrays_and_slices() {
        let mut xs: Vec<i32, 12> = Vec::new();
        xs.push(1).unwrap();

        let array = [1];

        assert_eq!(xs, array);
        assert_eq!(array, xs);

        assert_eq!(xs, array.as_slice());
        assert_eq!(array.as_slice(), xs);

        assert_eq!(xs, &array);
        assert_eq!(&array, xs);

        let longer_array = [1; 20];

        assert_ne!(xs, longer_array);
        assert_ne!(longer_array, xs);
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
        assert_eq!(&vec, slice);
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

        assert_eq!(Droppable::count(), 0);

        {
            let mut vec: Vec<Droppable, 2> = Vec::new();
            vec.push(Droppable::new()).ok().unwrap();
            vec.push(Droppable::new()).ok().unwrap();
            let _items = vec.into_iter();
            // Move none
        }

        assert_eq!(Droppable::count(), 0);

        {
            let mut vec: Vec<Droppable, 2> = Vec::new();
            vec.push(Droppable::new()).ok().unwrap();
            vec.push(Droppable::new()).ok().unwrap();
            let mut items = vec.into_iter();
            let _ = items.next(); // Move partly
        }

        assert_eq!(Droppable::count(), 0);
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
        v.resize(5, 0).expect_err("full");
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
    fn from_array() {
        // Successful construction, N == M
        let v: Vec<u8, 3> = Vec::from_array([1, 2, 3]);
        assert_eq!(v, Vec::<u8, 3>::from([1, 2, 3]));
        assert_eq!(v.len(), 3);
        assert_eq!(v.as_slice(), &[1, 2, 3]);

        // Successful construction, N > M
        let v: Vec<u8, 4> = Vec::from_array([1, 2, 3]);
        assert_eq!(v, Vec::<u8, 4>::from([1, 2, 3]));
        assert_eq!(v.len(), 3);
        assert_eq!(v.as_slice(), &[1, 2, 3]);
    }

    #[test]
    fn from_array_no_drop() {
        struct Drops(Option<u8>);

        impl Drop for Drops {
            fn drop(&mut self) {
                self.0 = None;
            }
        }

        let v: Vec<Drops, 3> = Vec::from([Drops(Some(1)), Drops(Some(2)), Drops(Some(3))]);

        assert_eq!(v[0].0, Some(1));
        assert_eq!(v[1].0, Some(2));
        assert_eq!(v[2].0, Some(3));
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

    #[test]
    fn zero_capacity() {
        let mut v: Vec<u8, 0> = Vec::new();
        // Validate capacity
        assert_eq!(v.capacity(), 0);

        // Make sure there is no capacity
        assert!(v.push(1).is_err());

        // Validate length
        assert_eq!(v.len(), 0);

        // Validate pop
        assert_eq!(v.pop(), None);

        // Validate slice
        assert_eq!(v.as_slice(), &[]);

        // Validate empty
        assert!(v.is_empty());

        // Validate full
        assert!(v.is_full());
    }
}

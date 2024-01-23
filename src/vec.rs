use core::{
    cmp::Ordering,
    fmt, hash,
    iter::FromIterator,
    mem,
    mem::{ManuallyDrop, MaybeUninit},
    ops, ptr, slice,
};

/// Workaround forbidden specialization of Drop
pub trait VecDrop {
    // SAFETY: drop_with_len will be called to call drop in place the first `len` elements of the buffer.
    // Only the Owned buffer (`[MaybeUninit<T>; N]`) must drop the items
    // and the view (`[MaybeUninit<T>]`) drops nothing.
    // `drop_with_len `assumes that the buffer can contain `len` elements.
    unsafe fn drop_with_len(&mut self, len: usize);
}

impl<T> VecDrop for [MaybeUninit<T>] {
    unsafe fn drop_with_len(&mut self, _len: usize) {
        // Case of a view, drop does nothing
    }
}

impl<T, const N: usize> VecDrop for [MaybeUninit<T>; N] {
    unsafe fn drop_with_len(&mut self, len: usize) {
        // NOTE(unsafe) avoid bound checks in the slicing operation
        // &mut buffer[..len]
        // SAFETY: buffer[..len] must be valid to drop given the safety requirement of the trait definition.
        let mut_slice = slice::from_raw_parts_mut(self.as_mut_ptr() as *mut T, len);
        // We drop each element used in the vector by turning into a `&mut [T]`.
        ptr::drop_in_place(mut_slice);
    }
}

/// <div class="warn">This is private API and should not be used</div>
pub struct VecInner<B: ?Sized + VecDrop> {
    len: usize,
    buffer: B,
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
/// vec.push(1).unwrap();
/// vec.push(2).unwrap();
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
/// In some cases, the const-generic might be cumbersome. `Vec` can coerce into a [`VecView`] to remove the need for the const-generic:
///
/// ```rust
/// use heapless::{Vec, VecView};
///
/// let vec: Vec<u8, 10> = Vec::from_slice(&[1, 2, 3, 4]).unwrap();
/// let view: &VecView<_> = &vec;
/// ```
pub type Vec<T, const N: usize> = VecInner<[MaybeUninit<T>; N]>;

/// A [`Vec`] with dynamic capacity
///
/// [`Vec`] coerces to `VecView`. `VecView` is `!Sized`, meaning it can only ever be used by reference.
///
/// Unlike [`Vec`], `VecView` does not have an `N` const-generic parameter.
/// This has the ergonomic advantage of making it possible to use functions without needing to know at
/// compile-time the size of the buffers used, for example for use in `dyn` traits.
///
/// `VecView<T>` is to `Vec<T, N>` what `[T]` is to `[T; N]`.
///
/// ```rust
/// use heapless::{Vec, VecView};
///
/// let mut vec: Vec<u8, 10> = Vec::from_slice(&[1, 2, 3, 4]).unwrap();
/// let view: &VecView<_> = &vec;
/// assert_eq!(view, &[1, 2, 3, 4]);
///
/// let mut_view: &mut VecView<_> = &mut vec;
/// mut_view.push(5);
/// assert_eq!(vec, [1, 2, 3, 4, 5]);
/// ```
pub type VecView<T> = VecInner<[MaybeUninit<T>]>;

impl<T> VecView<T> {
    /// Returns a raw pointer to the vector’s buffer.
    pub fn as_ptr(&self) -> *const T {
        self.buffer.as_ptr() as *const T
    }

    /// Returns a raw pointer to the vector’s buffer, which may be mutated through.
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.buffer.as_mut_ptr() as *mut T
    }

    /// Extracts a slice containing the entire vector.
    ///
    /// Equivalent to `&s[..]`.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::{Vec, VecView};
    /// let buffer: &VecView<u8> = &Vec::<u8, 5>::from_slice(&[1, 2, 3, 5, 8]).unwrap();
    /// assert_eq!(buffer.as_slice(), &[1, 2, 3, 5, 8]);
    /// ```
    pub fn as_slice(&self) -> &[T] {
        // NOTE(unsafe) avoid bound checks in the slicing operation
        // &buffer[..self.len]
        unsafe { slice::from_raw_parts(self.buffer.as_ptr() as *const T, self.len) }
    }

    /// Extracts a mutable slice containing the entire vector.
    ///
    /// Equivalent to `&mut s[..]`.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::{Vec, VecView};
    /// let mut buffer: &mut VecView<u8> = &mut Vec::<u8, 5>::from_slice(&[1, 2, 3, 5, 8]).unwrap();
    /// let buffer_slice = buffer.as_mut_slice();
    /// buffer_slice[0] = 9;
    /// assert_eq!(buffer.as_slice(), &[9, 2, 3, 5, 8]);
    /// ```
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        // NOTE(unsafe) avoid bound checks in the slicing operation
        // &mut buffer[..self.len]
        unsafe { slice::from_raw_parts_mut(self.buffer.as_mut_ptr() as *mut T, self.len) }
    }

    /// Returns the maximum number of elements the vector can hold.
    pub const fn capacity(&self) -> usize {
        self.buffer.len()
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
    /// use heapless::{Vec, VecView};
    ///
    /// let vec: &mut VecView<u8> = &mut Vec::<u8, 8>::new();
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
        self.buffer.get_unchecked_mut(self.len).as_ptr().read()
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

        *self.buffer.get_unchecked_mut(self.len) = MaybeUninit::new(item);

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
    /// use heapless::{Vec, VecView};
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
    ///     let mut dict_view: &mut VecView<_> = &mut dict;
    ///     let mut dict_length = 0;
    ///     // SAFETY: When `deflateGetDictionary` returns `Z_OK`, it holds that:
    ///     // 1. `dict_length` elements were initialized.
    ///     // 2. `dict_length` <= the capacity (32_768)
    ///     // which makes `set_len` safe to call.
    ///     unsafe {
    ///         // Make the FFI call...
    ///         let r = deflateGetDictionary(self.strm, dict_view.as_mut_ptr(), &mut dict_length);
    ///         if r == Z_OK {
    ///             // ...and update the length to what was initialized.
    ///             dict_view.set_len(dict_length);
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
    /// use heapless::{Vec, VecView};
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
    ///     vec.as_mut_view().set_len(0);
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
    /// use heapless::{Vec, VecView};
    ///
    /// let v: &mut VecView<_> = &mut Vec::<_, 8>::new();
    /// v.push("foo").unwrap();
    /// v.push("bar").unwrap();
    /// v.push("baz").unwrap();
    /// v.push("qux").unwrap();
    ///
    /// assert_eq!(v.swap_remove(1), "bar");
    /// assert_eq!(v, &["foo", "qux", "baz"]);
    ///
    /// assert_eq!(v.swap_remove(0), "foo");
    /// assert_eq!(v, &["baz", "qux"]);
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
    /// use heapless::{Vec, VecView};
    ///
    /// let mut v: &mut VecView<_> = &mut Vec::<_, 8>::new();
    /// v.push("foo").unwrap();
    /// v.push("bar").unwrap();
    /// v.push("baz").unwrap();
    /// v.push("qux").unwrap();
    ///
    /// assert_eq!(unsafe { v.swap_remove_unchecked(1) }, "bar");
    /// assert_eq!(v, &["foo", "qux", "baz"]);
    ///
    /// assert_eq!(unsafe { v.swap_remove_unchecked(0) }, "foo");
    /// assert_eq!(v, &["baz", "qux"]);
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
    /// use heapless::{Vec, VecView};
    ///
    /// let v: &VecView<_> = &Vec::<_, 8>::from_slice(b"abc").unwrap();
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
    /// use heapless::{Vec, VecView};
    ///
    /// let v: &VecView<_> = &Vec::<_, 8>::from_slice(b"abc").unwrap();
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
    /// use heapless::{Vec, VecView};
    ///
    /// let mut vec: &mut VecView<_> = &mut Vec::<_, 8>::from_slice(&[1, 2, 3]).unwrap();
    /// vec.insert(1, 4);
    /// assert_eq!(vec, &[1, 4, 2, 3]);
    /// vec.insert(4, 5);
    /// assert_eq!(vec, &[1, 4, 2, 3, 5]);
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
    /// use heapless::{Vec, VecView};
    ///
    /// let mut v: &mut VecView<_> = &mut Vec::<_, 8>::from_slice(&[1, 2, 3]).unwrap();
    /// assert_eq!(v.remove(1), 2);
    /// assert_eq!(v, &[1, 3]);
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
    /// use heapless::{Vec, VecView};
    ///
    /// let mut vec: &mut VecView<_> = &mut Vec::<_, 8>::from_slice(&[1, 2, 3, 4]).unwrap();
    /// vec.retain(|&x| x % 2 == 0);
    /// assert_eq!(vec, &[2, 4]);
    /// ```
    ///
    /// Because the elements are visited exactly once in the original order,
    /// external state may be used to decide which elements to keep.
    ///
    /// ```
    /// use heapless::{Vec, VecView};
    ///
    /// let mut vec: &mut VecView<_> = &mut Vec::<_, 8>::from_slice(&[1, 2, 3, 4, 5]).unwrap();
    /// let keep = [false, true, true, false, true];
    /// let mut iter = keep.iter();
    /// vec.retain(|_| *iter.next().unwrap());
    /// assert_eq!(vec, &[2, 3, 5]);
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
    /// use heapless::{Vec, VecView};
    ///
    /// let mut vec: &mut VecView<_> = &mut Vec::<_, 8>::from_slice(&[1, 2, 3, 4]).unwrap();
    /// vec.retain_mut(|x| {
    ///     if *x <= 3 {
    ///         *x += 1;
    ///         true
    ///     } else {
    ///         false
    ///     }
    /// });
    /// assert_eq!(vec, &[2, 3, 4]);
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
        struct BackshiftOnDrop<'a, T> {
            v: &'a mut VecView<T>,
            processed_len: usize,
            deleted_cnt: usize,
            original_len: usize,
        }

        impl<T> Drop for BackshiftOnDrop<'_, T> {
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

        fn process_loop<F, T, const DELETED: bool>(
            original_len: usize,
            f: &mut F,
            g: &mut BackshiftOnDrop<'_, T>,
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
        process_loop::<F, T, false>(original_len, &mut f, &mut g);

        // Stage 2: Some elements were deleted.
        process_loop::<F, T, true>(original_len, &mut f, &mut g);

        // All item are processed. This can be optimized to `set_len` by LLVM.
        drop(g);
    }

    /// Returns the remaining spare capacity of the vector as a slice of `MaybeUninit<T>`.
    ///
    /// The returned slice can be used to fill the vector with data before marking the data as
    /// initialized using the `set_len` method.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::{Vec, VecView};
    ///
    /// // Allocate vector big enough for 10 elements.
    /// let mut v: Vec<_, 10> = Vec::new();
    /// let view: &mut VecView<_> = &mut v;
    ///
    /// // Fill in the first 3 elements.
    /// let uninit = view.spare_capacity_mut();
    /// uninit[0].write(0);
    /// uninit[1].write(1);
    /// uninit[2].write(2);
    ///
    /// // Mark the first 3 elements of the vector as being initialized.
    /// unsafe {
    ///     view.set_len(3);
    /// }
    ///
    /// assert_eq!(view, &[0, 1, 2]);
    /// ```
    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<T>] {
        &mut self.buffer[self.len..]
    }
}

impl<T, const N: usize> Vec<T, N> {
    const ELEM: MaybeUninit<T> = MaybeUninit::uninit();
    const INIT: [MaybeUninit<T>; N] = [Self::ELEM; N]; // important for optimization of `new`

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
            buffer: Self::INIT,
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

    /// Get a reference to the Vec, erasing the `N` const-generic
    ///
    /// This can also be used through type coerction, since `Vec<T, N>` implements `Unsize<VecView<T>>`:
    ///
    /// ```rust
    /// use heapless::{Vec, VecView};
    ///
    /// let vec: Vec<u8, 10> = Vec::from_slice(&[1, 2, 3, 4]).unwrap();
    /// let view: &VecView<_> = &vec;
    /// ```
    pub const fn as_view(&self) -> &VecView<T> {
        self
    }

    /// Get a `mut` reference to the Vec, erasing the `N` const-generic
    ///
    /// This can also be used through type coerction, since `Vec<T, N>` implements `Unsize<VecView<T>>`:
    ///
    /// ```rust
    /// use heapless::{Vec, VecView};
    ///
    /// let mut vec: Vec<u8, 10> = Vec::from_slice(&[1, 2, 3, 4]).unwrap();
    /// let view: &mut VecView<_> = &mut vec;
    /// ```
    pub fn as_mut_view(&mut self) -> &mut VecView<T> {
        self
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
        self.as_view().as_slice()
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
            let array = unsafe { (&self.buffer as *const _ as *const [T; M]).read() };

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
    /// let buffer_slice = buffer.as_mut_slice();
    /// buffer_slice[0] = 9;
    /// assert_eq!(buffer.as_slice(), &[9, 2, 3, 5, 8]);
    /// ```
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self.as_mut_view().as_mut_slice()
    }

    /// Returns the maximum number of elements the vector can hold.
    pub const fn capacity(&self) -> usize {
        N
    }

    /// Clears the vector, removing all values.
    pub fn clear(&mut self) {
        self.as_mut_view().clear()
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
        self.as_mut_view().extend(iter)
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
        self.as_mut_view().extend_from_slice(other)
    }

    /// Removes the last element from a vector and returns it, or `None` if it's empty
    pub fn pop(&mut self) -> Option<T> {
        self.as_mut_view().pop()
    }

    /// Appends an `item` to the back of the collection
    ///
    /// Returns back the `item` if the vector is full
    pub fn push(&mut self, item: T) -> Result<(), T> {
        self.as_mut_view().push(item)
    }

    /// Removes the last element from a vector and returns it
    ///
    /// # Safety
    ///
    /// This assumes the vec to have at least one element.
    pub unsafe fn pop_unchecked(&mut self) -> T {
        self.as_mut_view().pop_unchecked()
    }

    /// Appends an `item` to the back of the collection
    ///
    /// # Safety
    ///
    /// This assumes the vec is not full.
    pub unsafe fn push_unchecked(&mut self, item: T) {
        self.as_mut_view().push_unchecked(item)
    }

    /// Shortens the vector, keeping the first `len` elements and dropping the rest.
    pub fn truncate(&mut self, len: usize) {
        self.as_mut_view().truncate(len)
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
        self.as_mut_view().resize(new_len, value)
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
        self.as_mut_view().resize_default(new_len)
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
        self.as_mut_view().swap_remove(index)
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
        self.as_mut_view().swap_remove_unchecked(index)
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
        self.as_mut_view().insert(index, element)
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
        self.as_mut_view().remove(index)
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
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.as_mut_view().retain(f)
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
    pub fn retain_mut<F>(&mut self, f: F)
    where
        F: FnMut(&mut T) -> bool,
    {
        self.as_mut_view().retain_mut(f)
    }

    /// Returns the remaining spare capacity of the vector as a slice of `MaybeUninit<T>`.
    ///
    /// The returned slice can be used to fill the vector with data before marking the data as
    /// initialized using the `set_len` method.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::Vec;
    ///
    /// // Allocate vector big enough for 10 elements.
    /// let mut v: Vec<_, 10> = Vec::new();
    ///
    /// // Fill in the first 3 elements.
    /// let uninit = v.spare_capacity_mut();
    /// uninit[0].write(0);
    /// uninit[1].write(1);
    /// uninit[2].write(2);
    ///
    /// // Mark the first 3 elements of the vector as being initialized.
    /// unsafe {
    ///     v.set_len(3);
    /// }
    ///
    /// assert_eq!(&v, &[0, 1, 2]);
    /// ```
    pub fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<T>] {
        self.as_mut_view().spare_capacity_mut()
    }
}

// Trait implementations

impl<T, const N: usize> Default for Vec<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> fmt::Debug for VecView<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <[T] as fmt::Debug>::fmt(self, f)
    }
}

impl<T, const N: usize> fmt::Debug for Vec<T, N>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_view().fmt(f)
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

impl fmt::Write for VecView<u8> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        match self.extend_from_slice(s.as_bytes()) {
            Ok(()) => Ok(()),
            Err(_) => Err(fmt::Error),
        }
    }
}

impl<T, const N: usize, const M: usize> From<[T; M]> for Vec<T, N> {
    fn from(array: [T; M]) -> Self {
        Self::from_array(array)
    }
}

impl<T: ?Sized + VecDrop> Drop for VecInner<T> {
    fn drop(&mut self) {
        // SAFETY: the buffer contains initialized data for the range 0..self.len
        unsafe { self.buffer.drop_with_len(self.len) }
    }
}

impl<'a, T: Clone, const N: usize> TryFrom<&'a [T]> for Vec<T, N> {
    type Error = ();

    fn try_from(slice: &'a [T]) -> Result<Self, Self::Error> {
        Vec::from_slice(slice)
    }
}

impl<T> Extend<T> for VecView<T> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        self.extend(iter)
    }
}

impl<T, const N: usize> Extend<T> for Vec<T, N> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = T>,
    {
        self.as_mut_view().extend(iter)
    }
}

impl<'a, T, const N: usize> Extend<&'a T> for Vec<T, N>
where
    T: 'a + Copy,
{
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = &'a T>,
    {
        self.as_mut_view().extend(iter.into_iter().cloned())
    }
}

impl<'a, T> Extend<&'a T> for VecView<T>
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

impl<T, const N: usize> hash::Hash for Vec<T, N>
where
    T: core::hash::Hash,
{
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.as_view().hash(state)
    }
}

impl<T> hash::Hash for VecView<T>
where
    T: core::hash::Hash,
{
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        <[T] as hash::Hash>::hash(self, state)
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a Vec<T, N> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_view().iter()
    }
}

impl<'a, T> IntoIterator for &'a VecView<T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a mut Vec<T, N> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_mut_view().iter_mut()
    }
}

impl<'a, T> IntoIterator for &'a mut VecView<T> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T, const N: usize> FromIterator<T> for Vec<T, N> {
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
pub struct IntoIter<T, const N: usize> {
    vec: Vec<T, N>,
    next: usize,
}

impl<T, const N: usize> Iterator for IntoIter<T, N> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        if self.next < self.vec.len() {
            let item = unsafe { self.vec.buffer.get_unchecked_mut(self.next).as_ptr().read() };
            self.next += 1;
            Some(item)
        } else {
            None
        }
    }
}

impl<T, const N: usize> Clone for IntoIter<T, N>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        let mut vec = Vec::new();

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

impl<T, const N: usize> Drop for IntoIter<T, N> {
    fn drop(&mut self) {
        unsafe {
            // Drop all the elements that have not been moved out of vec
            ptr::drop_in_place(&mut self.vec.as_mut_slice()[self.next..]);
            // Prevent dropping of other elements
            self.vec.len = 0;
        }
    }
}

impl<T, const N: usize> IntoIterator for Vec<T, N> {
    type Item = T;
    type IntoIter = IntoIter<T, N>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter { vec: self, next: 0 }
    }
}

impl<A, B, const N1: usize, const N2: usize> PartialEq<Vec<B, N2>> for Vec<A, N1>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &Vec<B, N2>) -> bool {
        self.as_view().eq(other.as_view())
    }
}

impl<A, B, const N: usize> PartialEq<Vec<B, N>> for VecView<A>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &Vec<B, N>) -> bool {
        self.eq(other.as_view())
    }
}

impl<A, B, const N: usize> PartialEq<VecView<B>> for Vec<A, N>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &VecView<B>) -> bool {
        self.as_view().eq(other)
    }
}

impl<A, B> PartialEq<VecView<B>> for VecView<A>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &VecView<B>) -> bool {
        <[A]>::eq(self, &**other)
    }
}

// Vec<A, N> == [B]
impl<A, B, const N: usize> PartialEq<[B]> for Vec<A, N>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &[B]) -> bool {
        self.as_view().eq(other)
    }
}

// VecView<A> == [B]
impl<A, B> PartialEq<[B]> for VecView<A>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &[B]) -> bool {
        <[A]>::eq(self, other)
    }
}

// [B] == Vec<A, N>
impl<A, B, const N: usize> PartialEq<Vec<A, N>> for [B]
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &Vec<A, N>) -> bool {
        other.as_view().eq(self)
    }
}

// [B] == VecView<A>
impl<A, B> PartialEq<VecView<A>> for [B]
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &VecView<A>) -> bool {
        <[A]>::eq(other, self)
    }
}

// Vec<A, N> == &[B]
impl<A, B, const N: usize> PartialEq<&[B]> for Vec<A, N>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &&[B]) -> bool {
        self.as_view().eq(other)
    }
}

// VecView<A> == &[B]
impl<A, B> PartialEq<&[B]> for VecView<A>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &&[B]) -> bool {
        <[A]>::eq(self, *other)
    }
}

// &[B] == Vec<A, N>
impl<A, B, const N: usize> PartialEq<Vec<A, N>> for &[B]
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &Vec<A, N>) -> bool {
        other.as_view().eq(self)
    }
}

// &[B] == VecView<A>
impl<A, B> PartialEq<VecView<A>> for &[B]
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &VecView<A>) -> bool {
        <[A]>::eq(other, *self)
    }
}

// Vec<A, N> == &mut [B]
impl<A, B, const N: usize> PartialEq<&mut [B]> for Vec<A, N>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &&mut [B]) -> bool {
        self.as_view().eq(other)
    }
}

// VecView<A> == &mut [B]
impl<A, B> PartialEq<&mut [B]> for VecView<A>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &&mut [B]) -> bool {
        <[A]>::eq(self, &other[..])
    }
}

// &mut [B] == Vec<A, N>
impl<A, B, const N: usize> PartialEq<Vec<A, N>> for &mut [B]
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &Vec<A, N>) -> bool {
        other.as_view().eq(self)
    }
}

// &mut [B] == VecView<A>
impl<A, B> PartialEq<VecView<A>> for &mut [B]
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &VecView<A>) -> bool {
        <[A]>::eq(other, &self[..])
    }
}

// Vec<A, N> == [B; M]
// Equality does not require equal capacity
impl<A, B, const N: usize, const M: usize> PartialEq<[B; M]> for Vec<A, N>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &[B; M]) -> bool {
        self.as_view().eq(other)
    }
}

// VecView<A, N> == [B; M]
// Equality does not require equal capacity
impl<A, B, const M: usize> PartialEq<[B; M]> for VecView<A>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &[B; M]) -> bool {
        <[A]>::eq(self, other)
    }
}

// [B; M] == Vec<A, N>
// Equality does not require equal capacity
impl<A, B, const N: usize, const M: usize> PartialEq<Vec<A, N>> for [B; M]
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &Vec<A, N>) -> bool {
        other.as_view().eq(self)
    }
}

// [B; M] == VecView<A>
// Equality does not require equal capacity
impl<A, B, const M: usize> PartialEq<VecView<A>> for [B; M]
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &VecView<A>) -> bool {
        <[A]>::eq(other, self)
    }
}

// Vec<A, N> == &[B; M]
// Equality does not require equal capacity
impl<A, B, const N: usize, const M: usize> PartialEq<&[B; M]> for Vec<A, N>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &&[B; M]) -> bool {
        self.as_view().eq(other)
    }
}

// VecView<A> == &[B; M]
// Equality does not require equal capacity
impl<A, B, const M: usize> PartialEq<&[B; M]> for VecView<A>
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &&[B; M]) -> bool {
        <[A]>::eq(self, *other)
    }
}

// &[B; M] == Vec<A, N>
// Equality does not require equal capacity
impl<A, B, const N: usize, const M: usize> PartialEq<Vec<A, N>> for &[B; M]
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &Vec<A, N>) -> bool {
        other.as_view().eq(self)
    }
}

// &[B; M] == VecView<A>
// Equality does not require equal capacity
impl<A, B, const M: usize> PartialEq<VecView<A>> for &[B; M]
where
    A: PartialEq<B>,
{
    fn eq(&self, other: &VecView<A>) -> bool {
        <[A]>::eq(other, *self)
    }
}

// Implements Eq if underlying data is Eq
impl<T, const N: usize> Eq for Vec<T, N> where T: Eq {}
impl<T> Eq for VecView<T> where T: Eq {}

impl<T, const N1: usize, const N2: usize> PartialOrd<Vec<T, N2>> for Vec<T, N1>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &Vec<T, N2>) -> Option<Ordering> {
        self.as_view().partial_cmp(other.as_view())
    }
}

impl<T> PartialOrd<VecView<T>> for VecView<T>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &VecView<T>) -> Option<Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }
}

impl<T, const N: usize> Ord for Vec<T, N>
where
    T: Ord,
{
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        Ord::cmp(&**self, &**other)
    }
}

impl<T, const N: usize> ops::Deref for Vec<T, N> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T, const N: usize> ops::DerefMut for Vec<T, N> {
    fn deref_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T> ops::Deref for VecView<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T> ops::DerefMut for VecView<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T, const N: usize> AsRef<Vec<T, N>> for Vec<T, N> {
    #[inline]
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<T, const N: usize> AsMut<Vec<T, N>> for Vec<T, N> {
    #[inline]
    fn as_mut(&mut self) -> &mut Self {
        self
    }
}

impl<T, const N: usize> AsRef<[T]> for Vec<T, N> {
    #[inline]
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T, const N: usize> AsMut<[T]> for Vec<T, N> {
    #[inline]
    fn as_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<T, const N: usize> Clone for Vec<T, N>
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

    #[test]
    fn spare_capacity_mut() {
        let mut v: Vec<_, 4> = Vec::new();
        let uninit = v.spare_capacity_mut();
        assert_eq!(uninit.len(), 4);
        uninit[0].write(1);
        uninit[1].write(2);
        uninit[2].write(3);
        unsafe { v.set_len(3) };
        assert_eq!(v.as_slice(), &[1, 2, 3]);

        let uninit = v.spare_capacity_mut();
        assert_eq!(uninit.len(), 1);
        uninit[0].write(4);
        unsafe { v.set_len(4) };
        assert_eq!(v.as_slice(), &[1, 2, 3, 4]);

        assert!(v.spare_capacity_mut().is_empty());
    }
}

use core::{
    fmt,
    ops::{Range, RangeBounds},
    ptr, slice,
};

use crate::LenType;

use super::VecView;

/// An iterator which uses a closure to determine if an element should be removed.
///
/// This struct is created by [`Vec::extract_if`].
/// See its documentation for more.
///
/// [`Vec::extract_if`]: crate::vec::VecInner::extract_if
///
/// # Example
///
/// ```
/// use heapless::Vec;
///
/// let mut v = Vec::<_, 4>::from_array([0, 1, 2]);
/// let iter: heapless::vec::ExtractIf<'_, _, _, _> = v.extract_if(.., |x| *x % 2 == 0);
/// ```
#[must_use = "iterators are lazy and do nothing unless consumed; \
    use `retain_mut` or `extract_if().for_each(drop)` to remove and discard elements"]
pub struct ExtractIf<'a, T, F, LenT: LenType> {
    vec: &'a mut VecView<T, LenT>,
    /// The index of the item that will be inspected by the next call to `next`.
    idx: usize,
    /// Elements at and beyond this point will be retained. Must be equal or smaller than
    /// `old_len`.
    end: usize,
    /// The number of items that have been drained (removed) thus far.
    del: usize,
    /// The original length of `vec` prior to draining.
    old_len: usize,
    /// The filter test predicate.
    pred: F,
}

impl<'a, T, F, LenT: LenType> ExtractIf<'a, T, F, LenT> {
    pub(super) fn new<R: RangeBounds<usize>>(
        vec: &'a mut VecView<T, LenT>,
        pred: F,
        range: R,
    ) -> Self {
        let old_len = vec.len();
        let Range { start, end } = crate::slice::range(range, ..old_len);

        // Guard against the vec getting leaked (leak amplification)
        unsafe {
            vec.set_len(0);
        }
        ExtractIf {
            vec,
            idx: start,
            del: 0,
            end,
            old_len,
            pred,
        }
    }
}

impl<T, F, LenT: LenType> Iterator for ExtractIf<'_, T, F, LenT>
where
    F: FnMut(&mut T) -> bool,
{
    type Item = T;

    fn next(&mut self) -> Option<T> {
        while self.idx < self.end {
            let i = self.idx;
            let buf_ptr = self.vec.as_mut_ptr();
            // SAFETY:
            //  We know that `i < self.end` from the if guard and that `self.end <= self.old_len`
            // from  the validity of `Self`. Therefore `i` points to an element within `vec`.
            //
            //  Additionally, the i-th element is valid because each element is visited at most once
            //  and it is the first time we access vec[i].
            //
            //  Note: we can't use `vec.get_unchecked_mut(i)` here since the precondition for that
            //  function is that i < vec.len(), but we've set vec's length to zero.
            let cur = unsafe { &mut *buf_ptr.add(i) };
            let drained = (self.pred)(cur);
            // Update the index *after* the predicate is called. If the index
            // is updated prior and the predicate panics, the element at this
            // index would be leaked.
            self.idx += 1;
            if drained {
                self.del += 1;
                // SAFETY: We never touch this element again after returning it.
                return Some(unsafe { ptr::read(cur) });
            } else if self.del > 0 {
                // SAFETY: `self.del` > 0, so the hole slot must not overlap with current element.
                // We use copy for move, and never touch this element again.
                unsafe {
                    let hole_slot = buf_ptr.add(i - self.del);
                    ptr::copy_nonoverlapping(cur, hole_slot, 1);
                }
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.end - self.idx))
    }
}

impl<T, F, LenT: LenType> Drop for ExtractIf<'_, T, F, LenT> {
    fn drop(&mut self) {
        if self.del > 0 {
            let ptr = self.vec.as_mut_ptr();
            // SAFETY: Trailing unchecked items must be valid since we never touch them.
            unsafe {
                ptr::copy(
                    ptr.cast_const().add(self.idx),
                    ptr.add(self.idx - self.del),
                    self.old_len - self.idx,
                );
            }
        }
        // SAFETY: After filling holes, all items are in contiguous memory.
        unsafe {
            self.vec.set_len(self.old_len - self.del);
        }
    }
}

impl<T, F, LenT: LenType> fmt::Debug for ExtractIf<'_, T, F, LenT>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // We have to use pointer arithmetic here,
        // because the length of `self.vec` is temporarily set to 0.
        let start = self.vec.as_ptr();

        // SAFETY: we always keep first `self.idx - self.del` elements valid.
        let retained = unsafe { slice::from_raw_parts(start, self.idx - self.del) };

        // SAFETY: we have not yet touched elements starting at `self.idx`.
        let valid_tail =
            unsafe { slice::from_raw_parts(start.add(self.idx), self.old_len - self.idx) };

        // SAFETY: `end - idx <= old_len - idx`, because `end <= old_len`. Also `idx <= end` by
        // invariant.
        let (remainder, skipped_tail) =
            unsafe { valid_tail.split_at_unchecked(self.end - self.idx) };

        f.debug_struct("ExtractIf")
            .field("retained", &retained)
            .field("remainder", &remainder)
            .field("skipped_tail", &skipped_tail)
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
mod tests {
    use super::super::Vec;

    #[test]
    fn extract_if_empty() {
        let mut vec = Vec::<i32, 8>::new();

        {
            let mut iter = vec.extract_if(.., |_| true);
            assert_eq!(iter.size_hint(), (0, Some(0)));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.size_hint(), (0, Some(0)));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.size_hint(), (0, Some(0)));
        }
        assert_eq!(vec.len(), 0);
        assert_eq!(vec, []);
    }

    #[test]
    fn extract_if_zst() {
        let mut vec = Vec::<(), 8>::from_array([(), (), (), (), ()]);
        let initial_len = vec.len();
        let mut count = 0;
        {
            let mut iter = vec.extract_if(.., |_| true);
            assert_eq!(iter.size_hint(), (0, Some(initial_len)));
            while let Some(_) = iter.next() {
                count += 1;
                assert_eq!(iter.size_hint(), (0, Some(initial_len - count)));
            }
            assert_eq!(iter.size_hint(), (0, Some(0)));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.size_hint(), (0, Some(0)));
        }

        assert_eq!(count, initial_len);
        assert_eq!(vec.len(), 0);
        assert_eq!(vec, []);
    }

    #[test]
    fn extract_if_false() {
        let mut vec = Vec::<_, 16>::from_array([1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);

        let initial_len = vec.len();
        let mut count = 0;
        {
            let mut iter = vec.extract_if(.., |_| false);
            assert_eq!(iter.size_hint(), (0, Some(initial_len)));
            for _ in iter.by_ref() {
                count += 1;
            }
            assert_eq!(iter.size_hint(), (0, Some(0)));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.size_hint(), (0, Some(0)));
        }

        assert_eq!(count, 0);
        assert_eq!(vec.len(), initial_len);
        assert_eq!(vec, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
    }

    #[test]
    fn extract_if_true() {
        let mut vec = Vec::<_, 16>::from_array([1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);

        let initial_len = vec.len();
        let mut count = 0;
        {
            let mut iter = vec.extract_if(.., |_| true);
            assert_eq!(iter.size_hint(), (0, Some(initial_len)));
            while let Some(_) = iter.next() {
                count += 1;
                assert_eq!(iter.size_hint(), (0, Some(initial_len - count)));
            }
            assert_eq!(iter.size_hint(), (0, Some(0)));
            assert_eq!(iter.next(), None);
            assert_eq!(iter.size_hint(), (0, Some(0)));
        }

        assert_eq!(count, initial_len);
        assert_eq!(vec.len(), 0);
        assert_eq!(vec, []);
    }

    #[test]
    fn extract_if_ranges() {
        let mut vec = Vec::<_, 16>::from_array([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);

        let mut count = 0;
        let it = vec.extract_if(1..=3, |_| {
            count += 1;
            true
        });
        assert_eq!(it.collect::<Vec<_, 8>>(), [1, 2, 3]);
        assert_eq!(vec, [0, 4, 5, 6, 7, 8, 9, 10]);
        assert_eq!(count, 3);

        let it = vec.extract_if(1..=3, |_| false);
        assert_eq!(it.collect::<Vec<_, 8>>(), []);
        assert_eq!(vec, [0, 4, 5, 6, 7, 8, 9, 10]);
    }

    #[test]
    #[should_panic]
    fn extract_if_out_of_bounds() {
        let mut vec = Vec::<_, 8>::from_array([0, 1]);
        vec.extract_if(5.., |_| true).for_each(drop);
    }

    #[test]
    fn extract_if_unconsumed() {
        let mut vec = Vec::<_, 4>::from_array([1, 2, 3, 4]);
        let drain = vec.extract_if(.., |&mut x| x % 2 != 0);
        drop(drain);
        assert_eq!(vec, [1, 2, 3, 4]);
    }

    #[test]
    fn extract_if_debug() {
        let mut vec = Vec::<_, 8>::from_array([1, 2, 3, 4, 5, 6, 7, 8]);
        let mut drain = vec.extract_if(1..5, |&mut x| x % 2 != 0);
        assert_eq!(
            format!("{drain:?}"),
            "ExtractIf { retained: [1], remainder: [2, 3, 4, 5], skipped_tail: [6, 7, 8], .. }"
        );
        drain.next().unwrap();
        assert_eq!(
            format!("{drain:?}"),
            "ExtractIf { retained: [1, 2], remainder: [4, 5], skipped_tail: [6, 7, 8], .. }"
        );
    }
}

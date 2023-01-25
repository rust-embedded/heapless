//! Bytes implementations for heapless types

use crate::Vec;
use bytes::buf::UninitSlice;
use bytes::BufMut;

unsafe impl<const N: usize> BufMut for Vec<u8, N> {
    #[inline]
    fn remaining_mut(&self) -> usize {
        N - self.len()
    }

    #[inline]
    unsafe fn advance_mut(&mut self, cnt: usize) {
        let len = self.len();
        let pos = len + cnt;
        if pos >= N {
            panic!("Advance out of range");
        }
        self.set_len(pos);
    }

    #[inline]
    fn chunk_mut(&mut self) -> &mut UninitSlice {
        let len = self.len();
        let ptr = self.as_mut_ptr();
        unsafe { &mut UninitSlice::from_raw_parts_mut(ptr, N)[len..] }
    }
}

#[cfg(test)]
mod tests {
    use crate::Vec;
    use bytes::BufMut;

    #[test]
    #[should_panic]
    fn advance_out_of_bound() {
        let mut vec: Vec<u8, 8> = Vec::new();
        unsafe { vec.advance_mut(9) };
    }

    #[test]
    fn remaining_mut() {
        let mut vec: Vec<u8, 8> = Vec::new();
        assert_eq!(vec.remaining_mut(), 8);
        vec.push(42).unwrap();
        assert_eq!(vec.remaining_mut(), 7);
    }

    #[test]
    fn chunk_mut() {
        let mut vec: Vec<u8, 8> = Vec::new();
        assert_eq!(vec.chunk_mut().len(), 8);
        unsafe { vec.advance_mut(1) };
        assert_eq!(vec.chunk_mut().len(), 7);
    }
}

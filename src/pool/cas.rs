//! Stack based on CAS atomics
//!
//! To reduce the chance of hitting the ABA problem we use a 32-bit offset + a 32-bit version tag
//! instead of a 64-bit pointer. The version tag will be bumped on each successful `pop` operation.

use core::{
    cell::UnsafeCell,
    convert::TryFrom,
    marker::PhantomData,
    mem::{self, MaybeUninit},
    num::NonZeroUsize,
    ptr::NonNull,
    sync::atomic::{AtomicUsize, Ordering},
};

/// Unfortunate implementation detail required to use the
/// [`Pool.grow_exact`](struct.Pool.html#method.grow_exact) method
pub struct Node<T> {
    next: Atomic<Node<T>>,
    pub(crate) data: UnsafeCell<T>,
}

impl<T> Node<T> {
    fn next(&self) -> &Atomic<Node<T>> {
        &self.next
    }
}

pub struct Stack<T> {
    head: Atomic<Node<T>>,
}

impl<T> Stack<T> {
    pub const fn new() -> Self {
        Self {
            head: Atomic::null(),
        }
    }

    pub fn push(&self, new_head: Ptr<Node<T>>) {
        let mut head = self.head.load(Ordering::Relaxed);

        loop {
            unsafe {
                new_head
                    .as_raw()
                    .as_ref()
                    .next()
                    .store(head, Ordering::Relaxed);
            }

            if let Err(p) = self.head.compare_and_exchange_weak(
                head,
                Some(new_head),
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                head = p;
            } else {
                return;
            }
        }
    }

    pub fn try_pop(&self) -> Option<Ptr<Node<T>>> {
        loop {
            if let Some(mut head) = self.head.load(Ordering::Acquire) {
                let next = unsafe { head.as_raw().as_ref().next().load(Ordering::Relaxed) };

                if self
                    .head
                    .compare_and_exchange_weak(
                        Some(head),
                        next,
                        Ordering::Release,
                        Ordering::Relaxed,
                    )
                    .is_ok()
                {
                    head.incr_tag();
                    return Some(head);
                }
            } else {
                // stack observed empty
                return None;
            }
        }
    }
}

fn anchor<T>() -> *mut T {
    static mut ANCHOR: u8 = 0;
    (unsafe { &mut ANCHOR } as *mut u8 as usize & !(mem::align_of::<T>() - 1)) as *mut T
}

/// Anchored pointer. This is a (signed) 32-bit offset from `anchor` plus a 32-bit tag
pub struct Ptr<T> {
    inner: NonZeroUsize,
    _marker: PhantomData<*mut T>,
}

impl<T> Clone for Ptr<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Ptr<T> {}

impl<T> Ptr<T> {
    pub fn new(p: *mut T) -> Option<Self> {
        i32::try_from((p as isize).wrapping_sub(anchor::<T>() as isize))
            .ok()
            .map(|offset| unsafe { Ptr::from_parts(0, offset) })
    }

    unsafe fn from_parts(tag: u32, offset: i32) -> Self {
        Self {
            inner: NonZeroUsize::new_unchecked((tag as usize) << 32 | (offset as u32 as usize)),
            _marker: PhantomData,
        }
    }

    fn from_usize(p: usize) -> Option<Self> {
        NonZeroUsize::new(p).map(|inner| Self {
            inner,
            _marker: PhantomData,
        })
    }

    fn into_usize(&self) -> usize {
        self.inner.get()
    }

    fn tag(&self) -> u32 {
        (self.inner.get() >> 32) as u32
    }

    fn incr_tag(&mut self) {
        let tag = self.tag().wrapping_add(1);
        let offset = self.offset();

        *self = unsafe { Ptr::from_parts(tag, offset) };
    }

    fn offset(&self) -> i32 {
        self.inner.get() as i32
    }

    fn as_raw(&self) -> NonNull<T> {
        unsafe {
            NonNull::new_unchecked(
                anchor::<T>()
                    .cast::<u8>()
                    .offset(self.offset() as isize)
                    .cast(),
            )
        }
    }

    pub fn dangling() -> Self {
        unsafe { Self::from_parts(0, 1) }
    }

    pub unsafe fn as_ref(&self) -> &T {
        &*self.as_raw().as_ptr()
    }
}

struct Atomic<T> {
    inner: AtomicUsize,
    _marker: PhantomData<*mut T>,
}

impl<T> Atomic<T> {
    const fn null() -> Self {
        Self {
            inner: AtomicUsize::new(0),
            _marker: PhantomData,
        }
    }

    fn compare_and_exchange_weak(
        &self,
        current: Option<Ptr<T>>,
        new: Option<Ptr<T>>,
        succ: Ordering,
        fail: Ordering,
    ) -> Result<(), Option<Ptr<T>>> {
        self.inner
            .compare_exchange_weak(
                current.map(|p| p.into_usize()).unwrap_or(0),
                new.map(|p| p.into_usize()).unwrap_or(0),
                succ,
                fail,
            )
            .map(drop)
            .map_err(Ptr::from_usize)
    }

    fn load(&self, ord: Ordering) -> Option<Ptr<T>> {
        NonZeroUsize::new(self.inner.load(ord)).map(|inner| Ptr {
            inner,
            _marker: PhantomData,
        })
    }

    fn store(&self, val: Option<Ptr<T>>, ord: Ordering) {
        self.inner
            .store(val.map(|p| p.into_usize()).unwrap_or(0), ord)
    }
}

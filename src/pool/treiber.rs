use core::{cell::UnsafeCell, mem::MaybeUninit};

#[cfg_attr(not(arm_llsc), path = "treiber/cas.rs")]
#[cfg_attr(arm_llsc, path = "treiber/llsc.rs")]
mod impl_;

pub use impl_::{AtomicPtr, NonNullPtr};

pub struct Stack<T> {
    top: AtomicPtr<Node<T>>,
}

impl<T> Stack<T> {
    pub const fn new() -> Self {
        Self {
            top: AtomicPtr::null(),
        }
    }

    /// # Safety
    /// - `node` must be a valid pointer
    /// - aliasing rules must be enforced by the caller. e.g, the same `node` may not be pushed more
    ///   than once
    /// - It must be valid to call `next()` on the `node`, meaning it must be properly initialized
    ///   for insertion into a stack/linked list
    pub unsafe fn push(&self, node: NonNullPtr<Node<T>>) {
        impl_::push(self, node);
    }

    pub fn try_pop(&self) -> Option<NonNullPtr<Node<T>>> {
        impl_::try_pop(self)
    }
}

pub struct Node<T> {
    pub next: AtomicPtr<Self>,
    pub data: UnsafeCell<MaybeUninit<T>>,
}

impl<T> Node<T> {
    /// Returns a new `Node` that does not contain data and is not linked to any other nodes.
    /// The return value of this function is guaranteed to have the `next` field properly
    /// initialized. Use this function if you want to insert a new `Node` into a linked
    /// list
    pub const fn unlinked() -> Self {
        Self {
            next: AtomicPtr::null(),
            data: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }

    unsafe fn next(this: *const Self) -> *const AtomicPtr<Self> {
        &raw const (*this).next
    }

    #[cfg_attr(not(arm_llsc), expect(unused))]
    unsafe fn next_mut(this: *mut Self) -> *mut AtomicPtr<Self> {
        &raw mut (*this).next
    }
}

#[cfg(test)]
mod tests {
    use core::mem;

    use super::*;

    #[test]
    fn node_is_never_zero_sized() {
        struct Zst;

        assert_ne!(mem::size_of::<Node<Zst>>(), 0);
    }
}

use core::{
    cell::UnsafeCell,
    mem::{ManuallyDrop, MaybeUninit},
};

#[cfg_attr(not(arm_llsc), path = "treiber/cas.rs")]
#[cfg_attr(arm_llsc, path = "treiber/llsc.rs")]
mod impl_;

pub use impl_::{AtomicPtr, NonNullPtr};

pub struct Stack<N>
where
    N: Node,
{
    top: AtomicPtr<N>,
}

impl<N> Stack<N>
where
    N: Node,
{
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
    pub unsafe fn push(&self, node: NonNullPtr<N>) {
        impl_::push(self, node);
    }

    pub fn try_pop(&self) -> Option<NonNullPtr<N>> {
        impl_::try_pop(self)
    }
}

pub trait Node: Sized {
    type Data;

    /// Returns a reference to the atomic pointer that stores the link to the next `Node`
    ///
    /// # Safety
    ///
    /// It must be valid to obtain a reference to the next link pointer, e.g. in the case of
    /// `UnionNode`, the `next` field must be properly initialized when calling this function
    unsafe fn next(this: *const Self) -> *const AtomicPtr<Self>;

    /// Returns a mutable reference to the atomic pointer that stores the link to the next `Node`
    ///
    /// # Safety
    ///
    /// It must be valid to obtain a reference to the next link pointer, e.g. in the case of
    /// `UnionNode`, the `next` field must be properly initialized when calling this function
    #[allow(dead_code)] // used conditionally
    unsafe fn next_mut(this: *mut Self) -> *mut AtomicPtr<Self>;
}

pub struct UnionNode<T> {
    pub next: AtomicPtr<Self>,
    pub data: UnsafeCell<MaybeUninit<T>>,
}

impl<T> UnionNode<T> {
    /// Returns a new `UnionNode` that does not contain data and is not linked to any other nodes.
    /// The return value of this function is guaranteed to have the `next` field properly
    /// initialized. Use this function if you want to insert a new `UnionNode` into a linked
    /// list
    pub const fn unlinked() -> Self {
        Self {
            next: AtomicPtr::null(),
            data: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }
}

impl<T> Node for UnionNode<T> {
    type Data = T;

    unsafe fn next(this: *const Self) -> *const AtomicPtr<Self> {
        &raw const (*this).next
    }

    unsafe fn next_mut(this: *mut Self) -> *mut AtomicPtr<Self> {
        &raw mut (*this).next
    }
}

pub struct StructNode<T> {
    pub next: AtomicPtr<Self>,
    pub data: ManuallyDrop<T>,
}

impl<T> Node for StructNode<T> {
    type Data = T;

    unsafe fn next(this: *const Self) -> *const AtomicPtr<Self> {
        &raw const (*this).next
    }

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

        assert_ne!(mem::size_of::<UnionNode<Zst>>(), 0);
    }
}

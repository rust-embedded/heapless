//! Stack based on LL/SC atomics

pub use core::ptr::NonNull as Ptr;
use core::{cell::UnsafeCell, ptr};

#[cfg(cas_atomic_polyfill)]
use atomic_polyfill::{AtomicPtr, Ordering};

#[cfg(not(cas_atomic_polyfill))]
use core::sync::atomic::{AtomicPtr, Ordering};

/// Unfortunate implementation detail required to use the
/// [`Pool.grow_exact`](struct.Pool.html#method.grow_exact) method
pub struct Node<T> {
    next: AtomicPtr<Node<T>>,
    pub(crate) data: UnsafeCell<T>,
}

impl<T> Node<T> {
    fn next(&self) -> &AtomicPtr<Node<T>> {
        &self.next
    }
}

pub struct Stack<T> {
    head: AtomicPtr<Node<T>>,
}

impl<T> Stack<T> {
    pub const fn new() -> Self {
        Self {
            head: AtomicPtr::new(ptr::null_mut()),
        }
    }

    pub fn push(&self, new_head: Ptr<Node<T>>) {
        // NOTE `Ordering`s come from crossbeam's (v0.6.0) `TreiberStack`

        let mut head = self.head.load(Ordering::Relaxed);
        loop {
            unsafe { new_head.as_ref().next().store(head, Ordering::Relaxed) }

            match self.head.compare_exchange_weak(
                head,
                new_head.as_ptr(),
                Ordering::Release, // success
                Ordering::Relaxed, // failure
            ) {
                Ok(_) => return,
                // interrupt occurred or other core made a successful STREX op on the head
                Err(p) => head = p,
            }
        }
    }

    pub fn try_pop(&self) -> Option<Ptr<Node<T>>> {
        // NOTE `Ordering`s come from crossbeam's (v0.6.0) `TreiberStack`

        loop {
            let head = self.head.load(Ordering::Acquire);
            if let Some(nn_head) = Ptr::new(head) {
                let next = unsafe { nn_head.as_ref().next().load(Ordering::Relaxed) };

                match self.head.compare_exchange_weak(
                    head,
                    next,
                    Ordering::Release, // success
                    Ordering::Relaxed, // failure
                ) {
                    Ok(_) => break Some(nn_head),
                    // interrupt occurred or other core made a successful STREX op on the head
                    Err(_) => continue,
                }
            } else {
                // stack is observed as empty
                break None;
            }
        }
    }
}

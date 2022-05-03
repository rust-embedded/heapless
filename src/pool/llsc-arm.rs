//! Stack based on LL/SC atomics

pub use core::ptr::NonNull as Ptr;
use core::{cell::UnsafeCell, ptr};

/// Unfortunate implementation detail required to use the
/// [`Pool.grow_exact`](struct.Pool.html#method.grow_exact) method
pub struct Node<T> {
    next: Option<Ptr<Node<T>>>,
    pub(crate) data: UnsafeCell<T>,
}

pub struct Stack<T> {
    top: Option<Ptr<Node<T>>>,
}

impl<T> Stack<T> {
    pub const fn new() -> Self {
        Self { top: None }
    }

    pub fn push(&self, mut node: Ptr<Node<T>>) {
        unsafe {
            let top_addr = ptr::addr_of!(self.top) as *mut usize;
            loop {
                let top = arch::load_link(top_addr);
                node.as_mut().next = Ptr::new(top as *mut _);
                if arch::store_conditional(node.as_ptr() as usize, top_addr).is_ok() {
                    break;
                }
            }
        }
    }

    pub fn try_pop(&self) -> Option<Ptr<Node<T>>> {
        unsafe {
            let top_addr = ptr::addr_of!(self.top) as *mut usize;
            loop {
                let top = arch::load_link(top_addr);
                if let Some(top) = Ptr::<Node<T>>::new(top as *mut _) {
                    let next = top.as_ref().next;
                    if arch::store_conditional(
                        next.map(|nn| nn.as_ptr() as usize).unwrap_or_default(),
                        top_addr,
                    )
                    .is_ok()
                    {
                        break Some(top);
                    }
                } else {
                    arch::clear_load_link();
                    break None;
                }
            }
        }
    }
}

#[cfg(target_arch = "arm")]
mod arch {
    use core::arch::asm;

    #[inline(always)]
    pub unsafe fn clear_load_link() {
        asm!("clrex", options(nomem, nostack));
    }

    #[inline(always)]
    pub unsafe fn load_link(addr: *const usize) -> usize {
        let value;
        asm!("ldrex {}, [{}]", out(reg) value, in(reg) addr, options(nostack));
        value
    }

    #[inline(always)]
    pub unsafe fn store_conditional(value: usize, addr: *mut usize) -> Result<(), ()> {
        let outcome: usize;
        asm!("strex {}, {}, [{}]", out(reg) outcome, in(reg) value, in(reg) addr, options(nostack));
        if outcome == 0 {
            Ok(())
        } else {
            Err(())
        }
    }
}

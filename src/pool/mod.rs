//! A heap-less, interrupt-safe, lock-free memory pool (\*)
//!
//! (\*) Currently, the implementation is only lock-free *and* `Sync` on ARMv7-M devices
//!
//! # Examples
//!
//! The most common way of using this pool is as a global singleton; the singleton mode gives you
//! automatic deallocation of memory blocks on `drop`.
//!
//! ``` ignore
//! #![no_main]
//! #![no_std]
//!
//! use heapless::{pool, pool::singleton::Box};
//!
//! // instantiate a memory pool of `[u8; 128]` blocks as a global singleton
//! pool!(
//!     // attributes can be used here
//!     // #[link_section = ".ccram.A"]
//!     A: [u8; 128]
//! );
//!
//! #[entry]
//! fn main() -> ! {
//!     static mut MEMORY: [u8; 1024] = [0; 1024];
//!
//!     // increase the capacity of the pool by ~8 blocks
//!     A::grow(MEMORY);
//!
//!     // claim a block of memory
//!     // note that the type is `Box<A>`, and not `Box<[u8; 128]>`
//!     // `A` is the "name" of the pool
//!     let x: Box<A, _> = A::alloc().unwrap();
//!     loop {
//!         // .. do stuff with `x` ..
//!     }
//! }
//!
//! #[exception]
//! fn SysTick() {
//!     // claim a block of memory
//!     let y = A::alloc().unwrap();
//!
//!     // .. do stuff with `y` ..
//!
//!     // return the memory block to the pool
//!     drop(y);
//! }
//! ```
//!
//! # Portability
//!
//! This pool internally uses a Treiber stack which is known to be susceptible to the ABA problem.
//! The only counter measure against the ABA problem that this implementation currently takes is
//! relying on LL/SC (Link-local / Store-conditional) instructions being used to implement CAS loops
//! on the target architecture (see section on ['Soundness'](#soundness) for more information). For
//! this reason, `Pool` only implements `Sync` when compiling for ARMv7-M.
//!
//! Also note that ARMv6-M architecture lacks the primitives for CAS loops so this module does *not*
//! exist for `thumbv6m-none-eabi`.
//!
//! # Soundness
//!
//! This pool uses a Treiber stack to keep a list of free memory blocks (nodes). Each of these
//! nodes has a pointer to the next node. To claim a memory block we simply pop a node from the
//! top of the stack and use it as a memory block. The pop operation consists of swapping the
//! current head (top) node with the node below it. The Rust code for the `pop` operation is shown
//! below:
//!
//! ``` ignore
//! fn pop(&self) -> Option<NonNull<Node<T>>> {
//!     let fetch_order = ..;
//!     let set_order = ..;
//!
//!     // `self.head` has type `AtomicPtr<Node<T>>`
//!     let mut head = self.head.load(fetch_order);
//!     loop {
//!         if let Some(nn_head) = NonNull::new(head) {
//!             let next = unsafe { (*head).next };
//!
//!             // <~ preempted
//!
//!             match self
//!                 .head
//!                 .compare_exchange_weak(head, next, set_order, fetch_order)
//!             {
//!                 Ok(_) => break Some(nn_head),
//!                 // head was changed by some interrupt handler / thread
//!                 Err(new_head) => head = new_head,
//!             }
//!         } else {
//!             // stack is observed as empty
//!             break None;
//!         }
//!     }
//! }
//! ```
//!
//! In general, the `pop` operation is susceptible to the ABA problem. If this operation gets
//! preempted by some interrupt handler somewhere between the `head.load` and the
//! `compare_and_exchange_weak`, and that handler modifies the stack in such a way that the head
//! (top) of the stack remains unchanged then resuming the `pop` operation will corrupt the stack.
//!
//! An example: imagine we are doing on `pop` on stack that contains these nodes: `A -> B -> C`,
//! `A` is the head (top), `B` is next to `A` and `C` is next to `B`. The `pop` operation will do a
//! `CAS(&self.head, A, B)` operation to atomically change the head to `B` iff it currently is `A`.
//! Now, let's say a handler preempts the `pop` operation before the `CAS` operation starts and it
//! `pop`s the stack twice and then `push`es back the `A` node; now the state of the stack is `A ->
//! C`. When the original `pop` operation is resumed it will succeed in doing the `CAS` operation
//! setting `B` as the head of the stack. However, `B` was used by the handler as a memory block and
//! no longer is a valid free node. As a result the stack, and thus the allocator, is in a invalid
//! state.
//!
//! However, not all is lost because Cortex-M devices use LL/SC (Link-local / Store-conditional)
//! operations to implement CAS loops. Let's look at the actual disassembly of `pop`.
//!
//! ``` text
//! 08000130 <<heapless::pool::Pool<T>>::pop>:
//!  8000130:       6802            ldr     r2, [r0, #0]
//!  8000132:       e00c            b.n     800014e <<heapless::pool::Pool<T>>::pop+0x1e>
//!  8000134:       4611            mov     r1, r2
//!  8000136:       f8d2 c000       ldr.w   ip, [r2]
//!  800013a:       e850 2f00       ldrex   r2, [r0]
//!  800013e:       428a            cmp     r2, r1
//!  8000140:       d103            bne.n   800014a <<heapless::pool::Pool<T>>::pop+0x1a>
//!  8000142:       e840 c300       strex   r3, ip, [r0]
//!  8000146:       b913            cbnz    r3, 800014e <<heapless::pool::Pool<T>>::pop+0x1e>
//!  8000148:       e004            b.n     8000154 <<heapless::pool::Pool<T>>::pop+0x24>
//!  800014a:       f3bf 8f2f       clrex
//!  800014e:       2a00            cmp     r2, #0
//!  8000150:       d1f0            bne.n   8000134 <<heapless::pool::Pool<T>>::pop+0x4>
//!  8000152:       2100            movs    r1, #0
//!  8000154:       4608            mov     r0, r1
//!  8000156:       4770            bx      lr
//! ```
//!
//! LDREX ("load exclusive") is the LL instruction, and STREX ("store exclusive") is the SC
//! instruction (see [1](#references)). On the Cortex-M, STREX will always fail if the processor
//! takes an exception between it and its corresponding LDREX operation (see [2](#references)). If
//! STREX fails then the CAS loop is retried (see instruction @ `0x8000146`). On single core
//! systems, preemption is required to run into the ABA problem and on Cortex-M devices preemption
//! always involves taking an exception. Thus the underlying LL/SC operations prevent the ABA
//! problem on Cortex-M.
//!
//! # References
//!
//! 1. [Cortex-M3 Devices Generic User Guide (DUI 0552A)][0], Section 2.2.7 "Synchronization
//! primitives"
//!
//! [0]: http://infocenter.arm.com/help/topic/com.arm.doc.dui0552a/DUI0552A_cortex_m3_dgug.pdf
//!
//! 2. [ARMv7-M Architecture Reference Manual (DDI 0403E.b)][1], Section A3.4 "Synchronization and
//! semaphores"
//!
//! [1]: https://static.docs.arm.com/ddi0403/eb/DDI0403E_B_armv7m_arm.pdf

#[cfg(not(armv6m))]
use core::{any::TypeId, mem, sync::atomic::Ordering};
use core::{
    cell::UnsafeCell,
    cmp, fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
    mem::MaybeUninit,
    ops::{Deref, DerefMut},
    ptr::{self, NonNull},
    sync::atomic::AtomicPtr,
};

use as_slice::{AsMutSlice, AsSlice};

pub mod singleton;

/// A lock-free memory pool
pub struct Pool<T> {
    head: AtomicPtr<Node<T>>,

    // Current implementation is unsound on architectures that don't have LL/SC semantics so this
    // struct is not `Sync` on those platforms
    _not_send_or_sync: PhantomData<*const ()>,
}

// NOTE: Here we lie about `Pool` implementing `Sync` on x86_64. This is not true but it lets us
// test the `pool!` and `singleton::Pool` abstractions. We just have to be careful not to use the
// pool in a multi-threaded context
#[cfg(any(armv7m, armv7r, test))]
unsafe impl<T> Sync for Pool<T> {}

unsafe impl<T> Send for Pool<T> {}

impl<T> Pool<T> {
    /// Creates a new empty pool
    pub const fn new() -> Self {
        Pool {
            head: AtomicPtr::new(ptr::null_mut()),

            _not_send_or_sync: PhantomData,
        }
    }

    /// Claims a memory block from the pool
    ///
    /// Returns `None` when the pool is observed as exhausted
    ///
    /// *NOTE:* This method does *not* have bounded execution time because it contains a CAS loop
    pub fn alloc(&self) -> Option<Box<T, Uninit>> {
        if let Some(node) = self.pop() {
            Some(Box {
                node,
                _state: PhantomData,
            })
        } else {
            None
        }
    }

    /// Returns a memory block to the pool
    ///
    /// *NOTE*: `T`'s destructor (if any) will run on `value` iff `S = Init`
    ///
    /// *NOTE:* This method does *not* have bounded execution time because it contains a CAS loop
    pub fn free<S>(&self, value: Box<T, S>)
    where
        S: 'static,
    {
        if TypeId::of::<S>() == TypeId::of::<Init>() {
            unsafe {
                ptr::drop_in_place(value.node.as_ref().data.get());
            }
        }

        self.push(value.node)
    }

    /// Increases the capacity of the pool
    ///
    /// This method might *not* fully utilize the given memory block due to alignment requirements.
    ///
    /// This method returns the number of *new* blocks that can be allocated.
    pub fn grow(&self, memory: &'static mut [u8]) -> usize {
        let mut p = memory.as_mut_ptr();
        let mut len = memory.len();

        let align = mem::align_of::<Node<T>>();
        let sz = mem::size_of::<Node<T>>();

        let rem = (p as usize) % align;
        if rem != 0 {
            let offset = align - rem;

            if offset >= len {
                // slice is too small
                return 0;
            }

            p = unsafe { p.add(offset) };
            len -= offset;
        }

        let mut n = 0;
        while len >= sz {
            self.push(unsafe { NonNull::new_unchecked(p as *mut _) });
            n += 1;

            p = unsafe { p.add(sz) };
            len -= sz;
        }

        n
    }

    /// Increases the capacity of the pool
    ///
    /// Unlike [`Pool.grow`](struct.Pool.html#method.grow) this method fully utilizes the given
    /// memory block
    pub fn grow_exact<A>(&self, memory: &'static mut MaybeUninit<A>) -> usize
    where
        A: AsMutSlice<Element = Node<T>>,
    {
        let nodes = unsafe { (*memory.as_mut_ptr()).as_mut_slice() };
        let cap = nodes.len();
        for p in nodes {
            self.push(NonNull::from(p))
        }
        cap
    }

    fn pop(&self) -> Option<NonNull<Node<T>>> {
        // NOTE `Ordering`s come from crossbeam's (v0.6.0) `TreiberStack`

        loop {
            let head = self.head.load(Ordering::Acquire);
            if let Some(nn_head) = NonNull::new(head) {
                let next = unsafe { (*head).next };

                match self.head.compare_exchange_weak(
                    head,
                    next,
                    Ordering::Release, // success
                    Ordering::Relaxed, // failure
                ) {
                    Ok(_) => break Some(nn_head),
                    // head was changed by some interrupt handler
                    Err(_) => continue,
                }
            } else {
                // stack is observed as empty
                break None;
            }
        }
    }

    fn push(&self, mut new_head: NonNull<Node<T>>) {
        // NOTE `Ordering`s come from crossbeam's (v0.6.0) `TreiberStack`

        let mut head = self.head.load(Ordering::Relaxed);
        loop {
            unsafe { new_head.as_mut().next = head }

            match self.head.compare_exchange_weak(
                head,
                new_head.as_ptr(),
                Ordering::Release, // success
                Ordering::Relaxed, // failure
            ) {
                Ok(_) => return,
                // head changed
                Err(p) => head = p,
            }
        }
    }
}

/// Unfortunate implementation detail required to use the
/// [`Pool.grow_exact`](struct.Pool.html#method.grow_exact) method
pub struct Node<T> {
    data: UnsafeCell<T>,
    next: *mut Node<T>,
}

/// A memory block
pub struct Box<T, STATE = Init> {
    _state: PhantomData<STATE>,
    node: NonNull<Node<T>>,
}

impl<T> Box<T, Uninit> {
    /// Initializes this memory block
    pub fn init(self, val: T) -> Box<T, Init> {
        unsafe {
            ptr::write(self.node.as_ref().data.get(), val);
        }

        Box {
            node: self.node,
            _state: PhantomData,
        }
    }
}

/// Uninitialized type state
pub enum Uninit {}

/// Initialized type state
pub enum Init {}

unsafe impl<T, S> Send for Box<T, S> where T: Send {}

unsafe impl<T, S> Sync for Box<T, S> where T: Sync {}

impl<A> AsSlice for Box<A>
where
    A: AsSlice,
{
    type Element = A::Element;

    fn as_slice(&self) -> &[A::Element] {
        self.deref().as_slice()
    }
}

impl<A> AsMutSlice for Box<A>
where
    A: AsMutSlice,
{
    fn as_mut_slice(&mut self) -> &mut [A::Element] {
        self.deref_mut().as_mut_slice()
    }
}

impl<T> Deref for Box<T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*self.node.as_ref().data.get() }
    }
}

impl<T> DerefMut for Box<T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.node.as_ref().data.get() }
    }
}

impl<T> fmt::Debug for Box<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <T as fmt::Debug>::fmt(self, f)
    }
}

impl<T> fmt::Display for Box<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <T as fmt::Display>::fmt(self, f)
    }
}

impl<T> PartialEq for Box<T>
where
    T: PartialEq,
{
    fn eq(&self, rhs: &Box<T>) -> bool {
        <T as PartialEq>::eq(self, rhs)
    }
}

impl<T> Eq for Box<T> where T: Eq {}

impl<T> PartialOrd for Box<T>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, rhs: &Box<T>) -> Option<cmp::Ordering> {
        <T as PartialOrd>::partial_cmp(self, rhs)
    }
}

impl<T> Ord for Box<T>
where
    T: Ord,
{
    fn cmp(&self, rhs: &Box<T>) -> cmp::Ordering {
        <T as Ord>::cmp(self, rhs)
    }
}

impl<T> Hash for Box<T>
where
    T: Hash,
{
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        <T as Hash>::hash(self, state)
    }
}

#[cfg(test)]
mod tests {
    use core::{
        mem::{self, MaybeUninit},
        sync::atomic::{AtomicUsize, Ordering},
    };

    use super::{Node, Pool};

    #[test]
    fn grow() {
        static mut MEMORY: [u8; 1024] = [0; 1024];

        static POOL: Pool<[u8; 128]> = Pool::new();

        unsafe {
            POOL.grow(&mut MEMORY);
        }

        for _ in 0..7 {
            assert!(POOL.alloc().is_some());
        }
    }

    #[test]
    fn grow_exact() {
        const SZ: usize = 8;
        static mut MEMORY: MaybeUninit<[Node<[u8; 128]>; SZ]> = MaybeUninit::uninit();

        static POOL: Pool<[u8; 128]> = Pool::new();

        unsafe {
            POOL.grow_exact(&mut MEMORY);
        }

        for _ in 0..SZ {
            assert!(POOL.alloc().is_some());
        }
        assert!(POOL.alloc().is_none());
    }

    #[test]
    fn sanity() {
        static mut MEMORY: [u8; 31] = [0; 31];

        static POOL: Pool<u8> = Pool::new();

        // empty pool
        assert!(POOL.alloc().is_none());

        POOL.grow(unsafe { &mut MEMORY });

        let x = POOL.alloc().unwrap().init(0);
        assert_eq!(*x, 0);

        // pool exhausted
        assert!(POOL.alloc().is_none());

        POOL.free(x);

        // should be possible to allocate again
        assert_eq!(*POOL.alloc().unwrap().init(1), 1);
    }

    #[test]
    fn destructors() {
        static COUNT: AtomicUsize = AtomicUsize::new(0);

        struct X;

        impl X {
            fn new() -> X {
                COUNT.fetch_add(1, Ordering::Relaxed);
                X
            }
        }

        impl Drop for X {
            fn drop(&mut self) {
                COUNT.fetch_sub(1, Ordering::Relaxed);
            }
        }

        static mut MEMORY: [u8; 31] = [0; 31];

        static POOL: Pool<X> = Pool::new();

        POOL.grow(unsafe { &mut MEMORY });

        let x = POOL.alloc().unwrap().init(X::new());
        let y = POOL.alloc().unwrap().init(X::new());
        let z = POOL.alloc().unwrap().init(X::new());

        assert_eq!(COUNT.load(Ordering::Relaxed), 3);

        // this leaks memory
        drop(x);

        assert_eq!(COUNT.load(Ordering::Relaxed), 3);

        // this leaks memory
        mem::forget(y);

        assert_eq!(COUNT.load(Ordering::Relaxed), 3);

        // this runs `X` destructor
        POOL.free(z);

        assert_eq!(COUNT.load(Ordering::Relaxed), 2);
    }
}

//! A heap-less, interrupt-safe, lock-free memory pool (\*)
//!
//! NOTE: This module is not available on targets that do *not* support CAS operations and are not
//! emulated by the [`atomic_polyfill`](https://crates.io/crates/atomic-polyfill) crate (e.g.,
//! MSP430).
//!
//! (\*) Currently, the implementation is only lock-free *and* `Sync` on ARMv6, ARMv7-{A,R,M} & ARMv8-M
//! devices
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
//! use cortex_m_rt::{entry, exception};
//! use heapless::{
//!     pool,
//!     pool::singleton::{Box, Pool},
//! };
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
//! this reason, `Pool` only implements `Sync` when compiling for some ARM cores.
//!
//! This module requires CAS atomic instructions which are not available on all architectures (e.g.
//! ARMv6-M (`thumbv6m-none-eabi`) and MSP430 (`msp430-none-elf`)). These atomics can be emulated
//! however with [`atomic_polyfill`](https://crates.io/crates/atomic-polyfill), which is enabled
//! with the `cas` feature and is enabled by default for `thumbv6m-none-eabi` and `riscv32` targets.
//! MSP430 is currently not supported by
//! [`atomic_polyfill`](https://crates.io/crates/atomic-polyfill).
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
//!     // where `struct Node<T> { next: AtomicPtr<Node<T>>, data: UnsafeCell<T> }`
//!     let mut head = self.head.load(fetch_order);
//!     loop {
//!         if let Some(nn_head) = NonNull::new(head) {
//!             let next = unsafe { (*head).next.load(Ordering::Relaxed) };
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
//! However, not all is lost because ARM devices use LL/SC (Link-local / Store-conditional)
//! operations to implement CAS loops. Let's look at the actual disassembly of `pop` for the ARM
//! Cortex-M.
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
//! In the case of multi-core systems if any other core successfully does a STREX op on the head
//! while the current core is somewhere between LDREX and STREX then the current core will fail its
//! STREX operation.
//!
//! # x86_64 support / limitations
//!
//! *NOTE* `Pool` is only `Sync` on `x86_64` and `x86` (`i686`) if the Cargo feature "x86-sync-pool"
//! is enabled
//!
//! x86_64 support is a gamble. Yes, a gamble. Do you feel lucky enough to use `Pool` on x86_64?
//!
//! As it's not possible to implement *ideal* LL/SC semantics (\*) on x86_64 the architecture is
//! susceptible to the ABA problem described above. To *reduce the chances* of ABA occurring in
//! practice we use version tags (keyword: IBM ABA-prevention tags). Again, this approach does
//! *not* fix / prevent / avoid the ABA problem; it only reduces the chance of it occurring in
//! practice but the chances of it occurring are not reduced to zero.
//!
//! How we have implemented version tags: instead of using an `AtomicPtr` to link the stack `Node`s
//! we use an `AtomicUsize` where the 64-bit `usize` is always comprised of a monotonically
//! increasing 32-bit tag (higher bits) and a 32-bit signed address offset. The address of a node is
//! computed by adding the 32-bit offset to an "anchor" address (the address of a static variable
//! that lives somewhere in the `.bss` linker section). The tag is increased every time a node is
//! popped (removed) from the stack.
//!
//! To see how version tags can prevent ABA consider the example from the previous section. Let's
//! start with a stack in this state: `(~A, 0) -> (~B, 1) -> (~C, 2)`, where `~A` represents the
//! address of node A as a 32-bit offset from the "anchor" and the second tuple element (e.g. `0`)
//! indicates the version of the node. For simplicity, assume a single core system: thread T1 is
//! performing `pop` and before `CAS(&self.head, (~A, 0), (~B, 1))` is executed a context switch
//! occurs and the core resumes T2. T2 pops the stack twice and pushes A back into the stack;
//! because the `pop` operation increases the version the stack ends in the following state: `(~A,
//! 1) -> (~C, 2)`. Now if T1 is resumed the CAS operation will fail because `self.head` is `(~A,
//! 1)` and not `(~A, 0)`.
//!
//! When can version tags fail to prevent ABA? Using the previous example: if T2 performs a `push`
//! followed by a `pop` `(1 << 32) - 1` times before doing its original `pop` - `pop` - `push`
//! operation then ABA will occur because the version tag of node `A` will wraparound to its
//! original value of `0` and the CAS operation in T1 will succeed and corrupt the stack.
//!
//! It does seem unlikely that (1) a thread will perform the above operation and (2) that the above
//! operation will complete within one time slice, assuming time sliced threads. If you have thread
//! priorities then the above operation could occur during the lifetime of many high priorities
//! threads if T1 is running at low priority.
//!
//! Other implementations of version tags use more than 32 bits in their tags (e.g. "Scalable
//! Lock-Free Dynamic Memory Allocation" uses 42-bit tags in its super blocks). In theory, one could
//! use double-word CAS on x86_64 to pack a 64-bit tag and a 64-bit pointer in a double-word but
//! this CAS operation is not exposed in the standard library (and I think it's not available on
//! older x86_64 processors?)
//!
//! (\*) Apparently one can emulate proper LL/SC semantics on x86_64 using hazard pointers (?) --
//! the technique appears to be documented in "ABA Prevention Using Single-Word Instructions", which
//! is not public AFAICT -- but hazard pointers require Thread Local Storage (TLS), which is a
//! non-starter for a `no_std` library like `heapless`.
//!
//! ## x86_64 Limitations
//!
//! *NOTE* this limitation does not apply to `x86` (32-bit address space). If you run into this
//! issue, on an x86_64 processor try running your code compiled for `x86`, e.g. `cargo run --target
//! i686-unknown-linux-musl`
//!
//! Because stack nodes must be located within +- 2 GB of the hidden `ANCHOR` variable, which
//! lives in the `.bss` section, `Pool` may not be able to manage static references created using
//! `Box::leak` -- these heap allocated chunks of memory may live in a very different address space.
//! When the `Pool` is unable to manage a node because of its address it will simply discard it:
//! `Pool::grow*` methods return the number of new memory blocks added to the pool; if these methods
//! return `0` it means the `Pool` is unable to manage the memory given to them.
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
//!
//! 3. "Scalable Lock-Free Dynamic Memory Allocation" Michael, Maged M.
//!
//! 4. "Hazard pointers: Safe memory reclamation for lock-free objects." Michael, Maged M.

use core::{any::TypeId, mem};
use core::{
    cmp, fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
    mem::MaybeUninit,
    ops::{Deref, DerefMut},
    ptr::{self, NonNull},
};

pub use stack::Node;
use stack::{Ptr, Stack};

pub mod singleton;
#[cfg_attr(any(target_arch = "x86_64", target_arch = "x86"), path = "cas.rs")]
#[cfg_attr(
    not(any(target_arch = "x86_64", target_arch = "x86")),
    path = "llsc.rs"
)]
mod stack;

/// A lock-free memory pool
pub struct Pool<T> {
    stack: Stack<T>,

    // Current implementation is unsound on architectures that don't have LL/SC semantics so this
    // struct is not `Sync` on those platforms
    _not_send_or_sync: PhantomData<*const ()>,
}

// NOTE(any(test)) makes testing easier (no need to enable Cargo features for testing)
#[cfg(any(
    armv6m,
    armv7a,
    armv7r,
    armv7m,
    armv8m_main,
    all(
        any(target_arch = "x86_64", target_arch = "x86"),
        feature = "x86-sync-pool"
    ),
    test
))]
unsafe impl<T> Sync for Pool<T> {}

unsafe impl<T> Send for Pool<T> {}

impl<T> Pool<T> {
    /// Creates a new empty pool
    pub const fn new() -> Self {
        Pool {
            stack: Stack::new(),

            _not_send_or_sync: PhantomData,
        }
    }

    /// Claims a memory block from the pool
    ///
    /// Returns `None` when the pool is observed as exhausted
    ///
    /// *NOTE:* This method does *not* have bounded execution time because it contains a CAS loop
    pub fn alloc(&self) -> Option<Box<T, Uninit>> {
        if mem::size_of::<T>() == 0 {
            // NOTE because we return a dangling pointer to a NODE, which has non-zero size
            // even when T is a ZST, in this case we need to make sure we
            // - don't do pointer arithmetic on this pointer
            // - dereference that offset-ed pointer as a ZST
            // because miri doesn't like that
            return Some(Box {
                node: Ptr::dangling(),
                _state: PhantomData,
            });
        }

        if let Some(node) = self.stack.try_pop() {
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
            let p = if mem::size_of::<T>() == 0 {
                // any pointer will do to invoke the destructor of a ZST
                NonNull::dangling().as_ptr()
            } else {
                unsafe { value.node.as_ref().data.get() }
            };
            unsafe {
                ptr::drop_in_place(p);
            }
        }

        // no operation
        if mem::size_of::<T>() == 0 {
            return;
        }

        self.stack.push(value.node)
    }

    /// Increases the capacity of the pool
    ///
    /// This method might *not* fully utilize the given memory block due to alignment requirements.
    ///
    /// This method returns the number of *new* blocks that can be allocated.
    pub fn grow(&self, memory: &'static mut [u8]) -> usize {
        if mem::size_of::<T>() == 0 {
            // ZST use no memory so a pool of ZST always has maximum capacity
            return usize::max_value();
        }

        let sz = mem::size_of::<Node<T>>();
        let mut p = memory.as_mut_ptr();
        let mut len = memory.len();

        let align = mem::align_of::<Node<T>>();
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
            match () {
                #[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
                () => {
                    if let Some(p) = Ptr::new(p as *mut _) {
                        self.stack.push(p);
                        n += 1;
                    }
                }

                #[cfg(not(any(target_arch = "x86_64", target_arch = "x86")))]
                () => {
                    self.stack.push(unsafe { Ptr::new_unchecked(p as *mut _) });
                    n += 1;
                }
            }

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
        A: AsMut<[Node<T>]>,
    {
        if mem::size_of::<T>() == 0 {
            return usize::max_value();
        }

        let nodes = unsafe { (*memory.as_mut_ptr()).as_mut() };
        let cap = nodes.len();
        for p in nodes {
            match () {
                #[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
                () => {
                    if let Some(p) = Ptr::new(p) {
                        self.stack.push(p);
                    }
                }

                #[cfg(not(any(target_arch = "x86_64", target_arch = "x86")))]
                () => self.stack.push(core::ptr::NonNull::from(p)),
            }
        }
        cap
    }
}

/// A memory block
pub struct Box<T, STATE = Init> {
    _state: PhantomData<STATE>,
    node: Ptr<Node<T>>,
}

impl<T> Box<T, Uninit> {
    /// Initializes this memory block
    pub fn init(self, val: T) -> Box<T, Init> {
        if mem::size_of::<T>() == 0 {
            // no memory operation needed for ZST
            // BUT we want to avoid calling `val`s destructor
            mem::forget(val)
        } else {
            unsafe {
                ptr::write(self.node.as_ref().data.get(), val);
            }
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

unsafe impl<T> stable_deref_trait::StableDeref for Box<T> {}

impl<A, T> AsRef<[T]> for Box<A>
where
    A: AsRef<[T]>,
{
    fn as_ref(&self) -> &[T] {
        self.deref().as_ref()
    }
}

impl<A, T> AsMut<[T]> for Box<A>
where
    A: AsMut<[T]>,
{
    fn as_mut(&mut self) -> &mut [T] {
        self.deref_mut().as_mut()
    }
}

impl<T> Deref for Box<T> {
    type Target = T;

    fn deref(&self) -> &T {
        if mem::size_of::<T>() == 0 {
            // any pointer will do for ZST
            unsafe { &*NonNull::dangling().as_ptr() }
        } else {
            unsafe { &*self.node.as_ref().data.get() }
        }
    }
}

impl<T> DerefMut for Box<T> {
    fn deref_mut(&mut self) -> &mut T {
        if mem::size_of::<T>() == 0 {
            // any pointer will do for ZST
            unsafe { &mut *NonNull::dangling().as_ptr() }
        } else {
            unsafe { &mut *self.node.as_ref().data.get() }
        }
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
        const SZ: usize = 2 * mem::size_of::<Node<u8>>() - 1;
        static mut MEMORY: [u8; SZ] = [0; SZ];

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

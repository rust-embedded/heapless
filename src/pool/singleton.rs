//! `Pool` as a global singleton

use core::{
    any::TypeId,
    cmp, fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
    mem::{self, MaybeUninit},
    ops::{Deref, DerefMut},
    ptr::{self, NonNull},
};

use super::{Init, Node, Uninit};

pub mod arc;

/// Instantiates a pool as a global singleton
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
#[macro_export]
macro_rules! pool {
    ($(#[$($attr:tt)*])* $ident:ident: $ty:ty) => {
        pub struct $ident;

        impl $crate::pool::singleton::Pool for $ident {
            type Data = $ty;

            fn ptr() -> &'static $crate::pool::Pool<$ty> {
                $(#[$($attr)*])*
                static $ident: $crate::pool::Pool<$ty> = $crate::pool::Pool::new();

                &$ident
            }
        }
    };
}

/// A global singleton memory pool
pub trait Pool {
    /// The type of data that can be allocated on this pool
    type Data: 'static;

    #[doc(hidden)]
    fn ptr() -> &'static super::Pool<Self::Data>;

    /// Claims a memory block from the pool
    ///
    /// Returns `None` when the pool is observed as exhausted
    ///
    /// *NOTE:* This method does *not* have bounded execution time; i.e. it contains a CAS loop
    fn alloc() -> Option<Box<Self, Uninit>>
    where
        Self: Sized,
    {
        Self::ptr().alloc().map(|inner| Box {
            _pool: PhantomData,
            inner,
        })
    }

    /// Increases the capacity of the pool
    ///
    /// This method might *not* fully utilize the given memory block due to alignment requirements
    ///
    /// This method returns the number of *new* blocks that can be allocated.
    fn grow(memory: &'static mut [u8]) -> usize {
        Self::ptr().grow(memory)
    }

    /// Increases the capacity of the pool
    ///
    /// Unlike [`Pool.grow`](trait.Pool.html#method.grow_exact) this method fully utilizes the given
    /// memory block
    fn grow_exact<A>(memory: &'static mut MaybeUninit<A>) -> usize
    where
        A: AsMut<[Node<Self::Data>]>,
    {
        Self::ptr().grow_exact(memory)
    }
}

/// A memory block that belongs to the global memory pool, `POOL`
pub struct Box<POOL, STATE = Init>
where
    POOL: Pool,
    STATE: 'static,
{
    _pool: PhantomData<POOL>,
    inner: super::Box<POOL::Data, STATE>,
}

impl<P> Box<P, Uninit>
where
    P: Pool,
{
    /// Initializes this memory block
    pub fn init(self, val: P::Data) -> Box<P, Init> {
        let node = self.inner.node;

        mem::forget(self);

        if mem::size_of::<P::Data>() == 0 {
            // no memory operation needed for ZST
            // BUT we want to avoid calling `val`s destructor
            mem::forget(val)
        } else {
            unsafe {
                ptr::write(node.as_ref().data.get(), val);
            }
        }

        Box {
            inner: super::Box {
                node,
                _state: PhantomData,
            },
            _pool: PhantomData,
        }
    }
}

impl<P> Box<P, Uninit>
where
    P: Pool,
    P::Data: AsRef<[u8]>,
{
    #[deprecated(
        since = "0.7.3",
        note = "This can access uninitialized memory, use `init(..)` instead (https://github.com/japaric/heapless/issues/212)"
    )]
    /// (DO NOT USE, SEE DEPRECATION) Freezes the contents of this memory block
    ///
    /// See [rust-lang/rust#58363](https://github.com/rust-lang/rust/pull/58363) for details.
    pub fn freeze(self) -> Box<P, Init> {
        let node = self.inner.node;

        mem::forget(self);

        // it seems we can get away with not calling `ptr::freeze` here and not run into UB
        // because we are dealing with static memory and using fences
        // let p: *const u8 = (*node.as_ref().data.get()).as_slice().as_ptr();
        // ptr::freeze(p as *mut u8);

        Box {
            inner: super::Box {
                node,
                _state: PhantomData,
            },
            _pool: PhantomData,
        }
    }
}

impl<P> Box<P, Init>
where
    P: Pool,
{
    /// Forgets the contents of this memory block without running its destructor.
    ///
    /// Note that this this does not return the memory block to the pool. The
    /// block can be reused, or returned to the pool by dropping it.
    pub fn forget(self) -> Box<P, Uninit> {
        let node = self.inner.node;

        mem::forget(self);
        if mem::size_of::<P::Data>() == 0 {
            // no need to do a pointer dereference in this case
        } else {
            mem::forget(unsafe { ptr::read(node.as_ref().data.get()) });
        }

        Box {
            inner: super::Box {
                node,
                _state: PhantomData,
            },
            _pool: PhantomData,
        }
    }
}

impl<P> Deref for Box<P>
where
    P: Pool,
{
    type Target = P::Data;

    fn deref(&self) -> &P::Data {
        self.inner.deref()
    }
}

impl<P> DerefMut for Box<P>
where
    P: Pool,
{
    fn deref_mut(&mut self) -> &mut P::Data {
        self.inner.deref_mut()
    }
}

unsafe impl<P: Pool> stable_deref_trait::StableDeref for Box<P> {}

impl<P> fmt::Debug for Box<P>
where
    P: Pool,
    P::Data: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <P::Data as fmt::Debug>::fmt(self, f)
    }
}

impl<P> fmt::Display for Box<P>
where
    P: Pool,
    P::Data: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <P::Data as fmt::Display>::fmt(self, f)
    }
}

impl<P, S> Drop for Box<P, S>
where
    P: Pool,
    S: 'static,
{
    fn drop(&mut self) {
        if TypeId::of::<S>() == TypeId::of::<Init>() {
            let p = if mem::size_of::<P::Data>() == 0 {
                // any pointer will do to invoke the destructor of a ZST
                NonNull::dangling().as_ptr()
            } else {
                unsafe { self.inner.node.as_ref().data.get() }
            };
            unsafe {
                ptr::drop_in_place(p);
            }
        }

        if mem::size_of::<P::Data>() != 0 {
            P::ptr().stack.push(self.inner.node)
        }
    }
}

unsafe impl<P, S> Send for Box<P, S>
where
    P: Pool,
    P::Data: Send,
{
}

unsafe impl<P, S> Sync for Box<P, S>
where
    P: Pool,
    P::Data: Sync,
{
}

impl<P, T> AsRef<[T]> for Box<P>
where
    P: Pool,
    P::Data: AsRef<[T]>,
{
    fn as_ref(&self) -> &[T] {
        self.deref().as_ref()
    }
}

impl<P, T> AsMut<[T]> for Box<P>
where
    P: Pool,
    P::Data: AsMut<[T]>,
{
    fn as_mut(&mut self) -> &mut [T] {
        self.deref_mut().as_mut()
    }
}

impl<P> PartialEq for Box<P>
where
    P: Pool,
    P::Data: PartialEq,
{
    fn eq(&self, rhs: &Box<P>) -> bool {
        <P::Data as PartialEq>::eq(self, rhs)
    }
}

impl<P> Eq for Box<P>
where
    P: Pool,
    P::Data: Eq,
{
}

impl<P> PartialOrd for Box<P>
where
    P: Pool,
    P::Data: PartialOrd,
{
    fn partial_cmp(&self, rhs: &Box<P>) -> Option<cmp::Ordering> {
        <P::Data as PartialOrd>::partial_cmp(self, rhs)
    }
}

impl<P> Ord for Box<P>
where
    P: Pool,
    P::Data: Ord,
{
    fn cmp(&self, rhs: &Box<P>) -> cmp::Ordering {
        <P::Data as Ord>::cmp(self, rhs)
    }
}

impl<P> Hash for Box<P>
where
    P: Pool,
    P::Data: Hash,
{
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        <P::Data as Hash>::hash(self, state)
    }
}

#[cfg(test)]
mod tests {
    use core::{
        mem,
        sync::atomic::{AtomicUsize, Ordering},
    };

    use super::{super::Node, Pool};

    #[test]
    fn sanity() {
        const SZ: usize = 2 * mem::size_of::<Node<u8>>() - 1;
        static mut MEMORY: [u8; SZ] = [0; SZ];

        pool!(A: u8);

        // empty pool
        assert!(A::alloc().is_none());

        A::grow(unsafe { &mut MEMORY });

        let x = A::alloc().unwrap().init(0);
        assert_eq!(*x, 0);

        // pool exhausted
        assert!(A::alloc().is_none());

        drop(x);

        // should be possible to allocate again
        assert_eq!(*A::alloc().unwrap().init(1), 1);
    }

    #[test]
    fn boxed_zst_is_well_aligned() {
        #[repr(align(2))]
        pub struct Zst2;

        pool!(A: Zst2);

        let x = A::alloc().unwrap().init(Zst2);
        assert_eq!(0, &*x as *const Zst2 as usize % 2);

        #[repr(align(4096))]
        pub struct Zst4096;

        pool!(B: Zst4096);

        let x = B::alloc().unwrap().init(Zst4096);
        assert_eq!(0, &*x as *const Zst4096 as usize % 4096);
    }

    #[test]
    fn destructors() {
        static COUNT: AtomicUsize = AtomicUsize::new(0);

        pub struct X;

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

        pool!(A: X);

        let x = A::alloc().unwrap().init(X::new());
        let y = A::alloc().unwrap().init(X::new());
        let z = A::alloc().unwrap().init(X::new());

        assert_eq!(COUNT.load(Ordering::Relaxed), 3);

        // this runs `X`'s destructor
        drop(x);

        assert_eq!(COUNT.load(Ordering::Relaxed), 2);

        // this leaks memory
        mem::forget(y);

        assert_eq!(COUNT.load(Ordering::Relaxed), 2);

        // this forgets `X` without leaking memory
        z.forget();

        assert_eq!(COUNT.load(Ordering::Relaxed), 2);
    }
}

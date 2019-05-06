//! `Pool` as a global singleton

use core::{
    any::TypeId,
    cmp, fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
    mem::{self, MaybeUninit},
    ops::{Deref, DerefMut},
    ptr,
};

use as_slice::{AsMutSlice, AsSlice};

use super::{Init, Node, Uninit};

/// Instantiates a pool as a global singleton
#[cfg(any(armv7m, armv7r, test))]
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
        A: AsMutSlice<Element = Node<Self::Data>>,
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

        unsafe {
            ptr::write(node.as_ref().data.get(), val);
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
    P::Data: AsSlice<Element = u8>,
{
    /// Freezes the contents of this memory block
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
            unsafe {
                ptr::drop_in_place(self.inner.node.as_ref().data.get());
            }
        }

        P::ptr().push(self.inner.node)
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

impl<P, T> AsSlice for Box<P>
where
    P: Pool,
    P::Data: AsSlice<Element = T>,
{
    type Element = T;

    fn as_slice(&self) -> &[T] {
        self.deref().as_slice()
    }
}

impl<P, T> AsMutSlice for Box<P>
where
    P: Pool,
    P::Data: AsMutSlice<Element = T>,
{
    fn as_mut_slice(&mut self) -> &mut [T] {
        self.deref_mut().as_mut_slice()
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

    use super::Pool;

    #[test]
    fn sanity() {
        static mut MEMORY: [u8; 31] = [0; 31];

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
        static mut MEMORY: [u8; 23] = [0; 23];

        A::grow(unsafe { &mut MEMORY });

        let x = A::alloc().unwrap().init(X::new());
        let y = A::alloc().unwrap().init(X::new());

        assert_eq!(COUNT.load(Ordering::Relaxed), 2);

        // this runs `X`'s destructor
        drop(x);

        assert_eq!(COUNT.load(Ordering::Relaxed), 1);

        // this leaks memory
        mem::forget(y);

        assert_eq!(COUNT.load(Ordering::Relaxed), 1);
    }
}

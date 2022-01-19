//! Like [`std::sync::Arc`](https://doc.rust-lang.org/std/sync/struct.Arc.html) but backed by a
//! memory [`Pool`](trait.Pool.html) rather than `#[global_allocator]`
//!
//! Note that the same limitations that apply to ["Box" pool] also apply to the "Arc" pool.
//!
//! ["Box" pool]: ../../index.html
//!
//! # Examples
//!
//! ``` ignore
//! use heapless::{arc_pool, Arc};
//!
//! pub struct BigStruct { // <- does NOT implement Clone
//!     data: [u8; 128],
//!     // ..
//! }
//!
//! // declare a memory pool
//! arc_pool!(P: BigStruct);
//!
//!
//! #[cortex_m_rt::entry]
//! fn main() -> ! {
//!     static mut MEMORY: [u8; 1024] = [0; 1024];
//!
//!     // give some static memory to the pool
//!     P::grow(MEMORY);
//!
//!     let x: Arc<P> = P::alloc(BigStruct::new()).ok().expect("OOM");
//!     //         ^ NOTE: this is the Pool type, not the data type
//!
//!     // cloning is cheap; it increases the refcount
//!     let y = x.clone();
//!
//!     // same data address
//!     assert_eq!(&*x as *const _, &*y as *const _);
//!
//!     // auto-deref
//!     let data: &[u8] = &x.data;
//!
//!     // decrease refcount
//!     drop(x);
//!
//!     // refcount decreased to 0; memory is returned to the pool
//!     drop(y);
//!
//!     // ..
//! }
//! ```
//!
//! The `grow_exact` API is also available on the "Arc pool". It requires using
//! `Node<ArcInner<Type>>` as the array element type. Example below:
//!
//! ``` ignore
//! use heapless::pool::{singleton::arc::ArcInner, Node};
//!
//! pub struct BigStruct { /* .. */ }
//!
//! arc_pool!(P: BigStruct);
//!
//! #[cortex_m_rt::entry]
//! fn main() -> ! {
//!     static mut MEMORY: MaybeUninit<[Node<ArcInner<BigStruct>>; 2]> = MaybeUninit::uninit();
//!
//!     P::grow_exact(MEMORY);
//!
//!     // 2 allocations are guaranteed to work
//!     let x = P::alloc(BigStruct::new()).ok().expect("OOM");
//!     let y = P::alloc(BigStruct::new()).ok().expect("OOM");
//!
//!     // ..
//! }
//! ```

use core::{
    cmp, fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
    ops::Deref,
    ptr,
    sync::atomic,
};

#[cfg(cas_atomic_polyfill)]
use atomic_polyfill::{AtomicUsize, Ordering};

#[cfg(not(cas_atomic_polyfill))]
use core::sync::atomic::{AtomicUsize, Ordering};

use crate::pool::{self, stack::Ptr, Node};

/// Instantiates a pool of Arc pointers as a global singleton
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
macro_rules! arc_pool {
    ($(#[$($attr:tt)*])* $ident:ident: $ty:ty) => {
        pub struct $ident;

        impl $crate::pool::singleton::arc::Pool for $ident {
            type Data = $ty;

            fn ptr() -> &'static $crate::pool::Pool<$crate::pool::singleton::arc::ArcInner<$ty>> {
                $(#[$($attr)*])*
                static POOL: $crate::pool::Pool<$crate::pool::singleton::arc::ArcInner<$ty>> =
                    $crate::pool::Pool::new();

                &POOL
            }
        }

        impl $ident {
            /// Allocates a new `Arc` and writes `data` to it
            ///
            /// Returns an `Err`or if the backing memory pool is empty
            pub fn alloc(data: $ty) -> Result<$crate::Arc<Self>, $ty>
            where
                Self: Sized,
            {
                $crate::Arc::new(data)
            }

            /// Increases the capacity of the pool
            ///
            /// This method might *not* fully utilize the given memory block due to alignment requirements
            ///
            /// This method returns the number of *new* blocks that can be allocated.
            pub fn grow(memory: &'static mut [u8]) -> usize {
                <Self as $crate::pool::singleton::arc::Pool>::ptr().grow(memory)
            }

            /// Increases the capacity of the pool
            ///
            /// Unlike `grow`, this method fully utilizes the given memory block
            pub fn grow_exact<A>(memory: &'static mut MaybeUninit<A>) -> usize
            where
                A: AsMut<[$crate::pool::Node<$crate::pool::singleton::arc::ArcInner<$ty>>]>,
            {
                <Self as $crate::pool::singleton::arc::Pool>::ptr().grow_exact(memory)
            }
        }
    };
}

/// Pool of Arc pointers
pub trait Pool {
    /// The data behind the Arc pointer
    type Data: 'static;

    #[doc(hidden)]
    fn ptr() -> &'static pool::Pool<ArcInner<Self::Data>>;
}

// mostly a verbatim copy of liballoc(/src/sync.rs) as of v1.54.0 minus the `Weak` API
// anything that diverges has been marked with `XXX`

/// `std::sync::Arc` but backed by a memory [`Pool`] rather than `#[global_allocator]`
///
/// [`Pool`]: trait.Pool.html
///
/// An example and more details can be found in the [module level documentation](index.html).
// XXX `Pool::Data` is not `?Sized` -- `Unsize` coercions cannot be implemented on stable
pub struct Arc<P>
where
    P: Pool,
{
    phantom: PhantomData<ArcInner<P::Data>>,
    ptr: Ptr<Node<ArcInner<P::Data>>>,
    pool: PhantomData<P>,
}

impl<P> Arc<P>
where
    P: Pool,
{
    /// Constructs a new `Arc`
    ///
    /// Returns an `Err`or if the backing memory pool is empty
    // XXX original API is "infallible"
    pub fn new(data: P::Data) -> Result<Self, P::Data> {
        if let Some(node) = P::ptr().stack.try_pop() {
            unsafe {
                ptr::write(
                    node.as_ref().data.get(),
                    ArcInner {
                        strong: AtomicUsize::new(1),
                        data,
                    },
                )
            }

            Ok(Self {
                phantom: PhantomData,
                pool: PhantomData,
                ptr: node,
            })
        } else {
            Err(data)
        }
    }

    fn inner(&self) -> &ArcInner<P::Data> {
        unsafe { &*self.ptr.as_ref().data.get() }
    }

    fn from_inner(ptr: Ptr<Node<ArcInner<P::Data>>>) -> Self {
        Self {
            phantom: PhantomData,
            pool: PhantomData,
            ptr,
        }
    }

    unsafe fn get_mut_unchecked(this: &mut Self) -> &mut P::Data {
        &mut (*this.ptr.as_ref().data.get()).data
        // &mut (*this.ptr.as_ptr()).data
    }

    #[inline(never)]
    unsafe fn drop_slow(&mut self) {
        // run `P::Data`'s destructor
        ptr::drop_in_place(Self::get_mut_unchecked(self));

        // XXX memory pool instead of `#[global_allocator]`
        // return memory to pool
        P::ptr().stack.push(self.ptr);
    }
}

const MAX_REFCOUNT: usize = (isize::MAX) as usize;

impl<P> AsRef<P::Data> for Arc<P>
where
    P: Pool,
{
    fn as_ref(&self) -> &P::Data {
        &**self
    }
}

// XXX no `Borrow` implementation due to 'conflicting implementations of trait' error

impl<P> Clone for Arc<P>
where
    P: Pool,
{
    fn clone(&self) -> Self {
        let old_size = self.inner().strong.fetch_add(1, Ordering::Relaxed);

        if old_size > MAX_REFCOUNT {
            // XXX original code calls `intrinsics::abort` which is unstable API
            panic!();
        }

        Self::from_inner(self.ptr)
    }
}

impl<P> fmt::Debug for Arc<P>
where
    P: Pool,
    P::Data: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<P> Deref for Arc<P>
where
    P: Pool,
{
    type Target = P::Data;

    fn deref(&self) -> &P::Data {
        &self.inner().data
    }
}

impl<P> fmt::Display for Arc<P>
where
    P: Pool,
    P::Data: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

// XXX original uses `#[may_dangle]` which is an unstable language feature
impl<P> Drop for Arc<P>
where
    P: Pool,
{
    fn drop(&mut self) {
        if self.inner().strong.fetch_sub(1, Ordering::Release) != 1 {
            return;
        }

        atomic::fence(Ordering::Acquire);

        unsafe {
            self.drop_slow();
        }
    }
}

impl<P> Eq for Arc<P>
where
    P: Pool,
    P::Data: Eq,
{
}

impl<P> Hash for Arc<P>
where
    P: Pool,
    P::Data: Hash,
{
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        (**self).hash(state)
    }
}

impl<P> Ord for Arc<P>
where
    P: Pool,
    P::Data: Ord,
{
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        (**self).cmp(&**other)
    }
}

impl<P> PartialEq for Arc<P>
where
    P: Pool,
    P::Data: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        // XXX missing pointer equality specialization, which uses an unstable language feature
        (**self).eq(&**other)
    }
}

impl<P> PartialOrd for Arc<P>
where
    P: Pool,
    P::Data: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        (**self).partial_cmp(&**other)
    }
}

unsafe impl<P> Send for Arc<P>
where
    P: Pool,
    P::Data: Sync + Send,
{
}

unsafe impl<P> Sync for Arc<P>
where
    P: Pool,
    P::Data: Sync + Send,
{
}

impl<P> Unpin for Arc<P> where P: Pool {}

/// Unfortunate implementation detail required to use the `grow_exact` API
pub struct ArcInner<T> {
    data: T,
    strong: AtomicUsize,
    // XXX `Weak` API not implemented
    // weak: AtomicUsize,
}

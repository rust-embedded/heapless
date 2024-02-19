use core::{marker::PhantomData, ptr::NonNull, sync::atomic::Ordering};

#[cfg(not(feature = "portable-atomic"))]
use core::sync::atomic;
#[cfg(feature = "portable-atomic")]
use portable_atomic as atomic;

use super::{Node, Stack};

#[cfg(target_pointer_width = "32")]
mod types {
    use super::atomic;

    pub type Inner = u64;
    pub type InnerAtomic = atomic::AtomicU64;
    pub type InnerNonZero = core::num::NonZeroU64;

    pub type Tag = core::num::NonZeroU32;
    pub type Address = u32;
}

#[cfg(target_pointer_width = "64")]
mod types {
    use super::atomic;

    pub type Inner = u128;
    pub type InnerAtomic = atomic::AtomicU128;
    pub type InnerNonZero = core::num::NonZeroU128;

    pub type Tag = core::num::NonZeroU64;
    pub type Address = u64;
}

use types::*;

pub struct AtomicPtr<N>
where
    N: Node,
{
    inner: InnerAtomic,
    _marker: PhantomData<*mut N>,
}

impl<N> AtomicPtr<N>
where
    N: Node,
{
    #[inline]
    pub const fn null() -> Self {
        Self {
            inner: InnerAtomic::new(0),
            _marker: PhantomData,
        }
    }

    fn compare_and_exchange_weak(
        &self,
        current: Option<NonNullPtr<N>>,
        new: Option<NonNullPtr<N>>,
        success: Ordering,
        failure: Ordering,
    ) -> Result<(), Option<NonNullPtr<N>>> {
        self.inner
            .compare_exchange_weak(
                current.map(NonNullPtr::into_inner).unwrap_or_default(),
                new.map(NonNullPtr::into_inner).unwrap_or_default(),
                success,
                failure,
            )
            .map(drop)
            .map_err(NonNullPtr::from_inner)
    }

    #[inline]
    fn load(&self, order: Ordering) -> Option<NonNullPtr<N>> {
        InnerNonZero::new(self.inner.load(order)).map(|inner| NonNullPtr {
            inner,
            _marker: PhantomData,
        })
    }

    #[inline]
    fn store(&self, value: Option<NonNullPtr<N>>, order: Ordering) {
        self.inner
            .store(value.map(NonNullPtr::into_inner).unwrap_or_default(), order)
    }
}

pub struct NonNullPtr<N>
where
    N: Node,
{
    inner: InnerNonZero,
    _marker: PhantomData<*mut N>,
}

impl<N> Clone for NonNullPtr<N>
where
    N: Node,
{
    fn clone(&self) -> Self {
        *self
    }
}

impl<N> Copy for NonNullPtr<N> where N: Node {}

impl<N> NonNullPtr<N>
where
    N: Node,
{
    #[inline]
    pub fn as_ptr(&self) -> *mut N {
        self.inner.get() as *mut N
    }

    #[inline]
    pub fn from_static_mut_ref(ref_: &'static mut N) -> NonNullPtr<N> {
        let non_null = NonNull::from(ref_);
        Self::from_non_null(non_null)
    }

    fn from_non_null(ptr: NonNull<N>) -> Self {
        let address = ptr.as_ptr() as Address;
        let tag = initial_tag().get();

        let value = (Inner::from(tag) << Address::BITS) | Inner::from(address);

        Self {
            inner: unsafe { InnerNonZero::new_unchecked(value) },
            _marker: PhantomData,
        }
    }

    #[inline]
    fn from_inner(value: Inner) -> Option<Self> {
        InnerNonZero::new(value).map(|inner| Self {
            inner,
            _marker: PhantomData,
        })
    }

    #[inline]
    fn non_null(&self) -> NonNull<N> {
        unsafe { NonNull::new_unchecked(self.as_ptr()) }
    }

    #[inline]
    fn into_inner(self) -> Inner {
        self.inner.get()
    }

    #[inline]
    fn tag(&self) -> Tag {
        unsafe { Tag::new_unchecked((self.inner.get() >> Address::BITS) as Address) }
    }

    fn increase_tag(&mut self) {
        let address = self.as_ptr() as Address;

        let new_tag = self.tag().checked_add(1).unwrap_or_else(initial_tag).get();

        let value = (Inner::from(new_tag) << Address::BITS) | Inner::from(address);

        self.inner = unsafe { InnerNonZero::new_unchecked(value) };
    }
}

#[inline]
const fn initial_tag() -> Tag {
    Tag::MIN
}

pub unsafe fn push<N>(stack: &Stack<N>, new_top: NonNullPtr<N>)
where
    N: Node,
{
    let mut top = stack.top.load(Ordering::Relaxed);

    loop {
        new_top
            .non_null()
            .as_ref()
            .next()
            .store(top, Ordering::Relaxed);

        if let Err(p) = stack.top.compare_and_exchange_weak(
            top,
            Some(new_top),
            Ordering::Release,
            Ordering::Relaxed,
        ) {
            top = p;
        } else {
            return;
        }
    }
}

pub fn try_pop<N>(stack: &Stack<N>) -> Option<NonNullPtr<N>>
where
    N: Node,
{
    loop {
        if let Some(mut top) = stack.top.load(Ordering::Acquire) {
            let next = unsafe { top.non_null().as_ref().next().load(Ordering::Relaxed) };

            if stack
                .top
                .compare_and_exchange_weak(Some(top), next, Ordering::Release, Ordering::Relaxed)
                .is_ok()
            {
                top.increase_tag();

                return Some(top);
            }
        } else {
            // stack observed as empty
            return None;
        }
    }
}

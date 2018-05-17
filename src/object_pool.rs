//! Object / memory pool

use core::any::TypeId;
use core::marker::PhantomData;
use core::{mem, ops, ptr};

use generic_array::{ArrayLength, GenericArray};
use stable_deref_trait::StableDeref;

/// Creates a singleton type that acts as a proxy for an uninitialized `static mut` variable
///
/// This type will provide an unsafe `new` constructor that can be used to create an instance of the
/// type. The caller must ensure that this constructor is called only *once* during the whole
/// lifetime of the program to avoid mutable aliasing.
///
/// # Example
///
/// ```
/// #[macro_use(singleton)]
/// extern crate heapless;
///
/// fn main() {
///     singleton!(A: i32);
///
///     let mut a = unsafe { A::new() }.init(1);
///
///     assert_eq!(*a, 1);
///
///     *a = 2;
///
///     let b: &'static mut i32 = a.into();
///
///     assert_eq!(*b, 2);
/// }
/// ```
#[macro_export]
macro_rules! singleton {
    ($Name:ident : $Type:ty) => {
        pub struct $Name {
            _0: $crate::object_pool::Private,
        }

        unsafe impl $crate::object_pool::Singleton for $Name {
            type Data = $Type;

            unsafe fn _var() -> &'static mut Self::Data {
                static mut VAR: $Type = unsafe { $crate::__core::mem::uninitialized() };

                &mut VAR
            }
        }

        impl $Name {
            unsafe fn new() -> $crate::object_pool::Uninit<Self> {
                $crate::object_pool::Uninit::new($Name {
                    _0: $crate::object_pool::Private::new(),
                })
            }
        }

        impl AsRef<$Type> for $Name {
            fn as_ref(&self) -> &$Type {
                use $crate::object_pool::Singleton;

                unsafe { $Name::_var() }
            }
        }

        impl AsMut<$Type> for $Name {
            fn as_mut(&mut self) -> &mut $Type {
                use $crate::object_pool::Singleton;

                unsafe { $Name::_var() }
            }
        }

        impl $crate::__core::ops::Deref for $Name {
            type Target = $Type;

            fn deref(&self) -> &$Type {
                self.as_ref()
            }
        }

        unsafe impl $crate::StableDeref for $Name {}

        impl $crate::__core::ops::DerefMut for $Name {
            fn deref_mut(&mut self) -> &mut $Type {
                self.as_mut()
            }
        }

        impl Into<&'static mut $Type> for $Name {
            fn into(self) -> &'static mut $Type {
                use $crate::object_pool::Singleton;

                unsafe { $Name::_var() }
            }
        }
    };
}

#[doc(hidden)]
pub struct Private {
    _0: (),
}

impl Private {
    #[doc(hidden)]
    pub unsafe fn new() -> Self {
        Private { _0: () }
    }
}

/// Uninitialized newtype
pub struct Uninit<S> {
    data: S,
}

impl<S> Uninit<S> {
    /// Wraps `data` in `Uninit` to indicate that it's uninitialized
    pub unsafe fn new(data: S) -> Self {
        Uninit { data }
    }

    /// Initializes the data to the given `value`
    pub fn init(self, value: S::Data) -> S
    where
        S: Singleton,
    {
        unsafe {
            ptr::write(S::_var(), value);
            self.data
        }
    }

    /// Leaves the data uninitialized
    pub fn noinit(self) -> S
    where
        S: Singleton,
        S::Data: Copy,
    {
        self.data
    }
}

/// [Type state] Uninitialized object
pub enum Uninitialized {}

/// [Type state] Initialized object
pub enum Initialized {}

/// An object that belongs to `POOL`
pub struct Object<POOL, STATE = Initialized> {
    index: u8,
    _pool: PhantomData<POOL>,
    _state: PhantomData<STATE>,
}

impl<P, S> Object<P, S> {
    fn get<T, N>(&self) -> *mut T
    where
        P: Singleton<Data = GenericArray<T, N>>,
        N: ArrayLength<T> + 'static,
        T: 'static,
    {
        unsafe { P::_var().get_unchecked_mut(usize::from(self.index)) }
    }
}

impl<P> Object<P, Uninitialized> {
    /// Initializes the object with the given `value`
    pub fn init<T, N>(self, value: T) -> Object<P, Initialized>
    where
        P: Singleton<Data = GenericArray<T, N>>,
        N: ArrayLength<T> + 'static,
        T: 'static,
    {
        unsafe {
            ptr::write(self.get(), value);

            Object {
                index: self.index,
                _pool: PhantomData,
                _state: PhantomData,
            }
        }
    }

    /// Leaves the object uninitialized
    pub fn noinit(self) -> Object<P, Initialized>
    where
        P: Singleton,
        P::Data: Copy,
    {
        Object {
            index: self.index,
            _pool: PhantomData,
            _state: PhantomData,
        }
    }
}

impl<T, N, P> ops::Deref for Object<P, Initialized>
where
    P: Singleton<Data = GenericArray<T, N>>,
    N: ArrayLength<T> + 'static,
    T: 'static,
{
    type Target = T;

    fn deref(&self) -> &T {
        // XXX `self.get` doesn't work here for some reason (inference error)
        unsafe { P::_var().get_unchecked(usize::from(self.index)) }
    }
}

unsafe impl<T, N, P> StableDeref for Object<P, Initialized>
where
    P: Singleton<Data = GenericArray<T, N>>,
    N: ArrayLength<T> + 'static,
    T: 'static,
{
}

impl<T, U, N, P> AsRef<U> for Object<P, Initialized>
where
    P: Singleton<Data = GenericArray<T, N>>,
    N: ArrayLength<T> + 'static,
    T: AsRef<U> + 'static,
    U: ?Sized,
{
    fn as_ref(&self) -> &U {
        (**self).as_ref()
    }
}

impl<T, U, N, P> AsMut<U> for Object<P, Initialized>
where
    P: Singleton<Data = GenericArray<T, N>>,
    N: ArrayLength<T> + 'static,
    T: AsMut<U> + 'static,
    U: ?Sized,
{
    fn as_mut(&mut self) -> &mut U {
        (**self).as_mut()
    }
}

impl<T, N, P> ops::DerefMut for Object<P, Initialized>
where
    P: Singleton<Data = GenericArray<T, N>>,
    N: ArrayLength<T> + 'static,
    T: 'static,
{
    fn deref_mut(&mut self) -> &mut T {
        // XXX `self.get` doesn't work here for some reason (inference error)
        unsafe { P::_var().get_unchecked_mut(usize::from(self.index)) }
    }
}

/// An unsafe marker trait for singleton types that act as proxies for a `static mut` variable
///
/// A type that implements this trait must also implement the following traits:
///
/// - `AsMut<Self::Data>`
/// - `AsRef<Self::Data>`
/// - `Deref<Target = Self::Data>`
/// - `DerefMut`
/// - `Into<&'static mut Self::Data>`
/// - `StableDeref`
pub unsafe trait Singleton {
    /// The data stored in the `static mut` variable
    type Data: 'static;

    #[doc(hidden)]
    unsafe fn _var() -> &'static mut Self::Data;
}

/// A pool of objects
pub struct ObjectPool<P> {
    _memory: PhantomData<P>,
    free: u8,
    head: u8,
    initialized: u8,
}

impl<P> ObjectPool<P> {
    /// Creates a new object pool from the given uninitialized memory
    ///
    /// # Panics
    ///
    /// This constructor panics if `P` is an array of zero sized values
    pub fn new<T, N>(_memory: Uninit<P>) -> Self
    where
        P: Singleton<Data = GenericArray<T, N>>,
        N: ArrayLength<T> + 'static,
        T: 'static,
    {
        assert!(mem::size_of::<T>() >= 1);

        ObjectPool {
            free: N::to_u8(),
            head: 0,
            initialized: 0,
            _memory: PhantomData,
        }
    }

    /// Gets an object from the pool, or returns `None` if the pool is currently empty
    pub fn get<T, N>(&mut self) -> Option<Object<P, Uninitialized>>
    where
        P: Singleton<Data = GenericArray<T, N>>,
        N: ArrayLength<T> + 'static,
        T: 'static,
    {
        unsafe {
            let cap = N::to_u8();

            if self.initialized < cap {
                let idx = self.initialized;
                *(P::_var().get_unchecked_mut(idx as usize) as *mut _ as *mut u8) = idx + 1;
                self.initialized += 1;
            }

            if self.free != 0 {
                let new_head =
                    *(P::_var().get_unchecked(usize::from(self.head)) as *const _ as *const u8);
                let index = self.head;
                self.head = new_head;

                self.free -= 1;

                Some(Object {
                    index,
                    _pool: PhantomData,
                    _state: PhantomData,
                })
            } else {
                None
            }
        }
    }

    /// Returns an object to the pool
    ///
    /// The `object` destructor will be called, if the object was initialized
    pub fn free<T, N, S>(&mut self, object: Object<P, S>)
    where
        P: Singleton<Data = GenericArray<T, N>>,
        N: ArrayLength<T> + 'static,
        T: 'static,
        S: 'static,
    {
        if TypeId::of::<S>() == TypeId::of::<Initialized>() {
            unsafe {
                ptr::drop_in_place(object.get());
            }
        }

        unsafe { *(object.get() as *mut u8) = self.head };

        self.free += 1;
        self.head = object.index;
    }
}

#[cfg(test)]
mod tests {
    use generic_array::typenum::consts::*;
    use generic_array::GenericArray;

    use super::{ObjectPool, Singleton};

    #[test]
    fn sanity() {
        singleton!(B: GenericArray<u8, U4>);

        let mut pool: ObjectPool<B> = ObjectPool::new(unsafe { B::new() });

        let _0 = pool.get().unwrap();
        assert_eq!(_0.index, 0);
        assert_eq!(pool.head, 1);
        assert_eq!(pool.free, 3);
        assert_eq!(pool.initialized, 1);

        let _1 = pool.get().unwrap();
        assert_eq!(_1.index, 1);
        assert_eq!(pool.head, 2);
        assert_eq!(pool.free, 2);
        assert_eq!(pool.initialized, 2);

        let _2 = pool.get().unwrap();
        assert_eq!(_2.index, 2);
        assert_eq!(pool.head, 3);
        assert_eq!(pool.free, 1);
        assert_eq!(pool.initialized, 3);

        pool.free(_0);
        assert_eq!(pool.head, 0);
        assert_eq!(pool.free, 2);
        assert_eq!(pool.initialized, 3);
        assert_eq!(unsafe { (*B::_var())[0] }, 3);

        pool.free(_2);
        assert_eq!(pool.head, 2);
        assert_eq!(pool.free, 3);
        assert_eq!(pool.initialized, 3);
        assert_eq!(unsafe { (*B::_var())[2] }, 0);

        let _2 = pool.get().unwrap();
        assert_eq!(_2.index, 2);
        assert_eq!(pool.head, 0);
        assert_eq!(pool.free, 2);
        assert_eq!(pool.initialized, 4);
        assert_eq!(unsafe { (*B::_var())[3] }, 4);
    }

    // test that deallocated values are dropped
    #[test]
    fn destructor() {
        static mut COUNT: usize = 0;

        pub struct A(u32);

        impl A {
            fn new() -> Self {
                unsafe { COUNT += 1 }
                A(0)
            }
        }

        impl Drop for A {
            fn drop(&mut self) {
                unsafe { COUNT -= 1 }
            }
        }

        singleton!(B: GenericArray<A, U4>);

        {
            let mut pool = ObjectPool::new(unsafe { B::new() });

            let _0 = pool.get().unwrap().init(A::new());
            assert_eq!(unsafe { COUNT }, 1);

            pool.free(_0);
            assert_eq!(unsafe { COUNT }, 0);
        }

        assert_eq!(unsafe { COUNT }, 0);
    }

    // test that values not explicitly deallocated are leaked
    #[test]
    fn leak() {
        static mut COUNT: usize = 0;

        pub struct A(u32);

        impl A {
            fn new() -> Self {
                unsafe { COUNT += 1 }
                A(0)
            }
        }

        impl Drop for A {
            fn drop(&mut self) {
                unsafe { COUNT -= 1 }
            }
        }

        singleton!(B: GenericArray<A, U4>);

        {
            let mut pool = ObjectPool::new(unsafe { B::new() });

            let _0 = pool.get().unwrap().init(A::new());
            assert_eq!(unsafe { COUNT }, 1);

            drop(_0);

            assert_eq!(unsafe { COUNT }, 1);

            let _1 = pool.get().unwrap().init(A::new());
            assert_eq!(unsafe { COUNT }, 2);

            drop(_1);

            assert_eq!(unsafe { COUNT }, 2);
        }

        assert_eq!(unsafe { COUNT }, 2);
    }

    // test that exhausting the pool and then deallocating works correctly
    #[test]
    fn empty() {
        singleton!(B: GenericArray<i8, U4>);

        let mut pool = ObjectPool::new(unsafe { B::new() });

        let _0 = pool.get().unwrap().init(-1);
        let _1 = pool.get().unwrap().init(-1);
        let _2 = pool.get().unwrap().init(-1);
        let _3 = pool.get().unwrap().init(-1);

        assert!(pool.get().is_none());

        pool.free(_0);
        pool.free(_2);

        let _2 = pool.get().unwrap().init(-1);
        assert_eq!(_2.index, 2);

        let _0 = pool.get().unwrap().init(-1);
        assert_eq!(_0.index, 0);
    }
}

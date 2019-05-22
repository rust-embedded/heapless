//! Fixed capacity Single Producer Single Consumer (SPSC) queue
//!
//! # Examples
//!
//! - `Queue` can be used as a plain queue
//!
//! ```
//! use heapless::spsc::Queue;
//! use heapless::consts::*;
//!
//! let mut rb: Queue<u8, U4> = Queue::new();
//!
//! assert!(rb.enqueue(0).is_ok());
//! assert!(rb.enqueue(1).is_ok());
//! assert!(rb.enqueue(2).is_ok());
//! assert!(rb.enqueue(3).is_ok());
//! assert!(rb.enqueue(4).is_err()); // full
//!
//! assert_eq!(rb.dequeue(), Some(0));
//! ```
//!
//! - `Queue` can be `split` and then be used in Single Producer Single Consumer mode
//!
//! ```
//! use heapless::spsc::Queue;
//! use heapless::consts::*;
//!
//! static mut Q: Queue<Event, U4> = Queue(heapless::i::Queue::new());
//!
//! enum Event { A, B }
//!
//! fn main() {
//!     // NOTE(unsafe) beware of aliasing the `consumer` end point
//!     let mut consumer = unsafe { Q.split().1 };
//!
//!     loop {
//!         // `dequeue` is a lockless operation
//!         match consumer.dequeue() {
//!             Some(Event::A) => { /* .. */ },
//!             Some(Event::B) => { /* .. */ },
//!             None => { /* sleep */ },
//!         }
//! #       break
//!     }
//! }
//!
//! // this is a different execution context that can preempt `main`
//! fn interrupt_handler() {
//!     // NOTE(unsafe) beware of aliasing the `producer` end point
//!     let mut producer = unsafe { Q.split().0 };
//! #   let condition = true;
//!
//!     // ..
//!
//!     if condition {
//!         producer.enqueue(Event::A).ok().unwrap();
//!     } else {
//!         producer.enqueue(Event::B).ok().unwrap();
//!     }
//!
//!     // ..
//! }
//! ```
//!
//! # Benchmarks
//!
//! Measured on a ARM Cortex-M3 core running at 8 MHz and with zero Flash wait cycles
//!
//! `-C opt-level`         |`3`|
//! -----------------------|---|
//! `Consumer<u8>::dequeue`| 15|
//! `Queue<u8>::dequeue`   | 12|
//! `Producer<u8>::enqueue`| 16|
//! `Queue<u8>::enqueue`   | 14|
//!
//! - All execution times are in clock cycles. 1 clock cycle = 125 ns.
//! - Execution time is *dependent* of `mem::size_of::<T>()`. Both operations include one
//! `memcpy(T)` in their successful path.
//! - The optimization level is indicated in the first row.
//! - The numbers reported correspond to the successful path (i.e. `Some` is returned by `dequeue`
//! and `Ok` is returned by `enqueue`).

use core::{cell::UnsafeCell, fmt, hash, marker::PhantomData, mem::MaybeUninit, ptr};

use generic_array::{ArrayLength, GenericArray};
use hash32;

use crate::sealed::spsc as sealed;
pub use split::{Consumer, Producer};

mod split;

/// Multi core synchronization - a memory barrier is used for synchronization
pub struct MultiCore;

/// Single core synchronization - no memory barrier synchronization, just a compiler fence
pub struct SingleCore;

// Atomic{U8,U16, Usize} with no CAS operations that works on targets that have "no atomic support"
// according to their specification
pub(crate) struct Atomic<U, C> {
    v: UnsafeCell<U>,
    c: PhantomData<C>,
}

impl<U, C> Atomic<U, C> {
    pub(crate) const fn new(v: U) -> Self {
        Atomic {
            v: UnsafeCell::new(v),
            c: PhantomData,
        }
    }
}

impl<U, C> Atomic<U, C>
where
    U: sealed::Uxx,
    C: sealed::XCore,
{
    fn get_mut(&mut self) -> &mut U {
        unsafe { &mut *self.v.get() }
    }

    fn load_acquire(&self) -> U {
        unsafe { U::load_acquire::<C>(self.v.get()) }
    }

    fn load_relaxed(&self) -> U {
        U::load_relaxed(self.v.get())
    }

    fn store_release(&self, val: U) {
        unsafe { U::store_release::<C>(self.v.get(), val) }
    }
}

/// A statically allocated single producer single consumer queue with a capacity of `N` elements
///
/// *IMPORTANT*: To get better performance use a capacity that is a power of 2 (e.g. `U16`, `U32`,
/// etc.).
///
/// By default `spsc::Queue` will use `usize` integers to hold the indices to its head and tail. For
/// small queues `usize` indices may be overkill. However, `spsc::Queue`'s index type is generic and
/// can be changed to `u8` or `u16` to reduce its footprint. The easiest to construct a
/// `spsc::Queue` with a smaller index type is to use the [`u8`] and [`u16`] constructors.
///
/// [`u8`]: struct.Queue.html#method.u8
/// [`u16`]: struct.Queue.html#method.u16
///
/// *IMPORTANT*: `spsc::Queue<_, _, u8>` has a maximum capacity of 255 elements; `spsc::Queue<_, _,
/// u16>` has a maximum capacity of 65535 elements.
///
/// `spsc::Queue` also comes in a single core variant. This variant can be created using the
/// following constructors: `u8_sc`, `u16_sc`, `usize_sc` and `new_sc`. This variant is `unsafe` to
/// create because the programmer must make sure that the queue's consumer and producer endpoints
/// (if split) are kept on a single core for their entire lifetime.
pub struct Queue<T, N, U = usize, C = MultiCore>(
    #[doc(hidden)] pub crate::i::Queue<GenericArray<T, N>, U, C>,
)
where
    N: ArrayLength<T>,
    U: sealed::Uxx,
    C: sealed::XCore;

impl<T, N, U, C> Queue<T, N, U, C>
where
    N: ArrayLength<T>,
    U: sealed::Uxx,
    C: sealed::XCore,
{
    /// Returns the maximum number of elements the queue can hold
    pub fn capacity(&self) -> U {
        U::truncate(N::to_usize())
    }

    /// Returns `true` if the queue has a length of 0
    pub fn is_empty(&self) -> bool {
        self.len_usize() == 0
    }

    /// Iterates from the front of the queue to the back
    pub fn iter(&self) -> Iter<'_, T, N, U, C> {
        Iter {
            rb: self,
            index: 0,
            len: self.len_usize(),
        }
    }

    /// Returns an iterator that allows modifying each value.
    pub fn iter_mut(&mut self) -> IterMut<'_, T, N, U, C> {
        let len = self.len_usize();
        IterMut {
            rb: self,
            index: 0,
            len,
        }
    }

    fn len_usize(&self) -> usize {
        let head = self.0.head.load_relaxed().into();
        let tail = self.0.tail.load_relaxed().into();

        tail.wrapping_sub(head)
    }
}

impl<T, N, U, C> Drop for Queue<T, N, U, C>
where
    N: ArrayLength<T>,
    U: sealed::Uxx,
    C: sealed::XCore,
{
    fn drop(&mut self) {
        for item in self {
            unsafe {
                ptr::drop_in_place(item);
            }
        }
    }
}

impl<T, N, U, C> fmt::Debug for Queue<T, N, U, C>
where
    N: ArrayLength<T>,
    T: fmt::Debug,
    U: sealed::Uxx,
    C: sealed::XCore,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T, N, U, C> hash::Hash for Queue<T, N, U, C>
where
    N: ArrayLength<T>,
    T: hash::Hash,
    U: sealed::Uxx,
    C: sealed::XCore,
{
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        // iterate over self in order
        for t in self.iter() {
            hash::Hash::hash(t, state);
        }
    }
}

impl<T, N, U, C> hash32::Hash for Queue<T, N, U, C>
where
    N: ArrayLength<T>,
    T: hash32::Hash,
    U: sealed::Uxx,
    C: sealed::XCore,
{
    fn hash<H: hash32::Hasher>(&self, state: &mut H) {
        // iterate over self in order
        for t in self.iter() {
            hash32::Hash::hash(t, state);
        }
    }
}

impl<'a, T, N, U, C> IntoIterator for &'a Queue<T, N, U, C>
where
    N: ArrayLength<T>,
    U: sealed::Uxx,
    C: sealed::XCore,
{
    type Item = &'a T;
    type IntoIter = Iter<'a, T, N, U, C>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T, N, U, C> IntoIterator for &'a mut Queue<T, N, U, C>
where
    N: ArrayLength<T>,
    U: sealed::Uxx,
    C: sealed::XCore,
{
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T, N, U, C>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

macro_rules! impl_ {
    ($uxx:ident, $uxx_sc:ident) => {
        impl<T, N> Queue<T, N, $uxx, MultiCore>
        where
            N: ArrayLength<T>,
        {
            /// Creates an empty queue with a fixed capacity of `N`
            pub fn $uxx() -> Self {
                Queue(crate::i::Queue::$uxx())
            }
        }

        impl<A> crate::i::Queue<A, $uxx, MultiCore> {
            /// `spsc::Queue` `const` constructor; wrap the returned value in
            /// [`spsc::Queue`](struct.Queue.html)
            pub const fn $uxx() -> Self {
                crate::i::Queue {
                    buffer: MaybeUninit::uninit(),
                    head: Atomic::new(0),
                    tail: Atomic::new(0),
                }
            }
        }

        impl<T, N> Queue<T, N, $uxx, SingleCore>
        where
            N: ArrayLength<T>,
        {
            /// Creates an empty queue with a fixed capacity of `N` (single core variant)
            pub unsafe fn $uxx_sc() -> Self {
                Queue(crate::i::Queue::$uxx_sc())
            }
        }

        impl<A> crate::i::Queue<A, $uxx, SingleCore> {
            /// `spsc::Queue` `const` constructor; wrap the returned value in
            /// [`spsc::Queue`](struct.Queue.html)
            pub const unsafe fn $uxx_sc() -> Self {
                crate::i::Queue {
                    buffer: MaybeUninit::uninit(),
                    head: Atomic::new(0),
                    tail: Atomic::new(0),
                }
            }
        }

        impl<T, N, C> Queue<T, N, $uxx, C>
        where
            N: ArrayLength<T>,
            C: sealed::XCore,
        {
            /// Returns the item in the front of the queue, or `None` if the queue is empty
            pub fn dequeue(&mut self) -> Option<T> {
                let cap = self.capacity();

                let head = self.0.head.get_mut();
                let tail = self.0.tail.get_mut();

                let p = self.0.buffer.as_ptr();

                if *head != *tail {
                    let item = unsafe { (p as *const T).add(usize::from(*head % cap)).read() };
                    *head = head.wrapping_add(1);
                    Some(item)
                } else {
                    None
                }
            }

            /// Adds an `item` to the end of the queue
            ///
            /// Returns back the `item` if the queue is full
            pub fn enqueue(&mut self, item: T) -> Result<(), T> {
                let cap = self.capacity();
                let head = *self.0.head.get_mut();
                let tail = *self.0.tail.get_mut();

                if tail.wrapping_sub(head) > cap - 1 {
                    Err(item)
                } else {
                    unsafe { self.enqueue_unchecked(item) }
                    Ok(())
                }
            }

            /// Adds an `item` to the end of the queue, without checking if it's full
            ///
            /// # Unsafety
            ///
            /// If the queue is full this operation will leak a value (T's destructor won't run on
            /// the value that got overwritten by `item`), *and* will allow the `dequeue` operation
            /// to create a copy of `item`, which could result in `T`'s destructor running on `item`
            /// twice.
            pub unsafe fn enqueue_unchecked(&mut self, item: T) {
                let cap = self.capacity();
                let tail = self.0.tail.get_mut();

                // NOTE(ptr::write) the memory slot that we are about to write to is
                // uninitialized. We use `ptr::write` to avoid running `T`'s destructor on the
                // uninitialized memory
                (self.0.buffer.as_mut_ptr() as *mut T)
                    .add(usize::from(*tail % cap))
                    .write(item);
                *tail = tail.wrapping_add(1);
            }

            /// Returns the number of elements in the queue
            pub fn len(&self) -> $uxx {
                let head = self.0.head.load_relaxed();
                let tail = self.0.tail.load_relaxed();

                if head > tail {
                    tail.wrapping_sub(head)
                } else {
                    tail - head
                }
            }
        }

        impl<T, N, C> Clone for Queue<T, N, $uxx, C>
        where
            T: Clone,
            N: ArrayLength<T>,
            C: sealed::XCore,
        {
            fn clone(&self) -> Self {
                let mut new: Queue<T, N, $uxx, C> = Queue(crate::i::Queue {
                    buffer: MaybeUninit::uninit(),
                    head: Atomic::new(0),
                    tail: Atomic::new(0),
                });

                for s in self.iter() {
                    unsafe {
                        // NOTE(unsafe) new.capacity() == self.capacity() <= self.len()
                        // no overflow possible
                        new.enqueue_unchecked(s.clone());
                    }
                }
                new
            }
        }
    };
}

impl<A> crate::i::Queue<A, usize, MultiCore> {
    /// `spsc::Queue` `const` constructor; wrap the returned value in
    /// [`spsc::Queue`](struct.Queue.html)
    pub const fn new() -> Self {
        crate::i::Queue::usize()
    }
}

impl<T, N> Queue<T, N, usize, MultiCore>
where
    N: ArrayLength<T>,
{
    /// Alias for [`spsc::Queue::usize`](struct.Queue.html#method.usize)
    pub fn new() -> Self {
        Queue(crate::i::Queue::new())
    }
}

impl<A> crate::i::Queue<A, usize, SingleCore> {
    /// `spsc::Queue` `const` constructor; wrap the returned value in
    /// [`spsc::Queue`](struct.Queue.html)
    pub const unsafe fn new_sc() -> Self {
        crate::i::Queue::usize_sc()
    }
}

impl<T, N> Queue<T, N, usize, SingleCore>
where
    N: ArrayLength<T>,
{
    /// Alias for [`spsc::Queue::usize_sc`](struct.Queue.html#method.usize_sc)
    pub unsafe fn new_sc() -> Self {
        Queue(crate::i::Queue::new_sc())
    }
}

impl_!(u8, u8_sc);
impl_!(u16, u16_sc);
impl_!(usize, usize_sc);

impl<T, N, U, C, N2, U2, C2> PartialEq<Queue<T, N2, U2, C2>> for Queue<T, N, U, C>
where
    T: PartialEq,
    N: ArrayLength<T>,
    U: sealed::Uxx,
    C: sealed::XCore,
    N2: ArrayLength<T>,
    U2: sealed::Uxx,
    C2: sealed::XCore,
{
    fn eq(&self, other: &Queue<T, N2, U2, C2>) -> bool {
        self.len_usize() == other.len_usize()
            && self.iter().zip(other.iter()).all(|(v1, v2)| v1 == v2)
    }
}

impl<T, N, U, C> Eq for Queue<T, N, U, C>
where
    T: Eq,
    N: ArrayLength<T>,
    U: sealed::Uxx,
    C: sealed::XCore,
{
}

/// An iterator over the items of a queue
pub struct Iter<'a, T, N, U, C>
where
    N: ArrayLength<T>,
    U: sealed::Uxx,
    C: sealed::XCore,
{
    rb: &'a Queue<T, N, U, C>,
    index: usize,
    len: usize,
}

impl<'a, T, N, U, C> Clone for Iter<'a, T, N, U, C>
where
    N: ArrayLength<T>,
    U: sealed::Uxx,
    C: sealed::XCore,
{
    fn clone(&self) -> Self {
        Self {
            rb: self.rb,
            index: self.index,
            len: self.len,
        }
    }
}

/// A mutable iterator over the items of a queue
pub struct IterMut<'a, T, N, U, C>
where
    N: ArrayLength<T>,
    U: sealed::Uxx,
    C: sealed::XCore,
{
    rb: &'a mut Queue<T, N, U, C>,
    index: usize,
    len: usize,
}

macro_rules! iterator {
    (struct $name:ident -> $elem:ty, $ptr:ty, $asptr:ident, $mkref:ident) => {
        impl<'a, T, N, U, C> Iterator for $name<'a, T, N, U, C>
        where
            N: ArrayLength<T>,
            U: sealed::Uxx,
            C: sealed::XCore,
        {
            type Item = $elem;

            fn next(&mut self) -> Option<$elem> {
                if self.index < self.len {
                    let head = self.rb.0.head.load_relaxed().into();

                    let cap = self.rb.capacity().into();
                    let ptr = self.rb.0.buffer.$asptr() as $ptr;
                    let i = (head + self.index) % cap;
                    self.index += 1;
                    Some(unsafe { $mkref!(*ptr.offset(i as isize)) })
                } else {
                    None
                }
            }
        }
    };
}

macro_rules! make_ref {
    ($e:expr) => {
        &($e)
    };
}

macro_rules! make_ref_mut {
    ($e:expr) => {
        &mut ($e)
    };
}

iterator!(struct Iter -> &'a T, *const T, as_ptr, make_ref);
iterator!(struct IterMut -> &'a mut T, *mut T, as_mut_ptr, make_ref_mut);

#[cfg(test)]
mod tests {
    use hash32::Hasher;

    use crate::{consts::*, spsc::Queue};

    #[test]
    fn static_new() {
        static mut _Q: Queue<i32, U4> = Queue(crate::i::Queue::new());
    }

    #[test]
    fn drop() {
        struct Droppable;
        impl Droppable {
            fn new() -> Self {
                unsafe {
                    COUNT += 1;
                }
                Droppable
            }
        }

        impl Drop for Droppable {
            fn drop(&mut self) {
                unsafe {
                    COUNT -= 1;
                }
            }
        }

        static mut COUNT: i32 = 0;

        {
            let mut v: Queue<Droppable, U4> = Queue::new();
            v.enqueue(Droppable::new()).ok().unwrap();
            v.enqueue(Droppable::new()).ok().unwrap();
            v.dequeue().unwrap();
        }

        assert_eq!(unsafe { COUNT }, 0);

        {
            let mut v: Queue<Droppable, U4> = Queue::new();
            v.enqueue(Droppable::new()).ok().unwrap();
            v.enqueue(Droppable::new()).ok().unwrap();
        }

        assert_eq!(unsafe { COUNT }, 0);
    }

    #[test]
    fn full() {
        let mut rb: Queue<i32, U4> = Queue::new();

        rb.enqueue(0).unwrap();
        rb.enqueue(1).unwrap();
        rb.enqueue(2).unwrap();
        rb.enqueue(3).unwrap();

        assert!(rb.enqueue(4).is_err());
    }

    #[test]
    fn iter() {
        let mut rb: Queue<i32, U4> = Queue::new();

        rb.enqueue(0).unwrap();
        rb.enqueue(1).unwrap();
        rb.enqueue(2).unwrap();

        let mut items = rb.iter();

        assert_eq!(items.next(), Some(&0));
        assert_eq!(items.next(), Some(&1));
        assert_eq!(items.next(), Some(&2));
        assert_eq!(items.next(), None);
    }

    #[test]
    fn iter_mut() {
        let mut rb: Queue<i32, U4> = Queue::new();

        rb.enqueue(0).unwrap();
        rb.enqueue(1).unwrap();
        rb.enqueue(2).unwrap();

        let mut items = rb.iter_mut();

        assert_eq!(items.next(), Some(&mut 0));
        assert_eq!(items.next(), Some(&mut 1));
        assert_eq!(items.next(), Some(&mut 2));
        assert_eq!(items.next(), None);
    }

    #[test]
    fn sanity() {
        let mut rb: Queue<i32, U4> = Queue::new();

        assert_eq!(rb.dequeue(), None);

        rb.enqueue(0).unwrap();

        assert_eq!(rb.dequeue(), Some(0));

        assert_eq!(rb.dequeue(), None);
    }

    #[test]
    #[cfg(feature = "smaller-atomics")]
    fn u8() {
        let mut rb: Queue<u8, U256, _> = Queue::u8();

        for _ in 0..255 {
            rb.enqueue(0).unwrap();
        }

        assert!(rb.enqueue(0).is_err());
    }

    #[test]
    fn wrap_around() {
        let mut rb: Queue<i32, U3> = Queue::new();

        rb.enqueue(0).unwrap();
        rb.enqueue(1).unwrap();
        rb.enqueue(2).unwrap();
        rb.dequeue().unwrap();
        rb.dequeue().unwrap();
        rb.dequeue().unwrap();
        rb.enqueue(3).unwrap();
        rb.enqueue(4).unwrap();

        assert_eq!(rb.len(), 2);
    }

    #[test]
    fn ready_flag() {
        let mut rb: Queue<i32, U2> = Queue::new();
        let (mut p, mut c) = rb.split();
        assert_eq!(c.ready(), false);
        assert_eq!(p.ready(), true);

        p.enqueue(0).unwrap();

        assert_eq!(c.ready(), true);
        assert_eq!(p.ready(), true);

        p.enqueue(1).unwrap();

        assert_eq!(c.ready(), true);
        assert_eq!(p.ready(), false);

        c.dequeue().unwrap();

        assert_eq!(c.ready(), true);
        assert_eq!(p.ready(), true);

        c.dequeue().unwrap();

        assert_eq!(c.ready(), false);
        assert_eq!(p.ready(), true);
    }

    #[test]
    fn clone() {
        let mut rb1: Queue<i32, U4> = Queue::new();
        rb1.enqueue(0).unwrap();
        rb1.enqueue(0).unwrap();
        rb1.dequeue().unwrap();
        rb1.enqueue(0).unwrap();
        let rb2 = rb1.clone();
        assert_eq!(rb1.capacity(), rb2.capacity());
        assert_eq!(rb1.len_usize(), rb2.len_usize());
        assert!(rb1.iter().zip(rb2.iter()).all(|(v1, v2)| v1 == v2));
    }

    #[test]
    fn eq() {
        // generate two queues with same content
        // but different buffer alignment
        let mut rb1: Queue<i32, U4> = Queue::new();
        rb1.enqueue(0).unwrap();
        rb1.enqueue(0).unwrap();
        rb1.dequeue().unwrap();
        rb1.enqueue(0).unwrap();
        let mut rb2: Queue<i32, U4> = Queue::new();
        rb2.enqueue(0).unwrap();
        rb2.enqueue(0).unwrap();
        assert!(rb1 == rb2);
        // test for symmetry
        assert!(rb2 == rb1);
        // test for changes in content
        rb1.enqueue(0).unwrap();
        assert!(rb1 != rb2);
        rb2.enqueue(1).unwrap();
        assert!(rb1 != rb2);
        // test for refexive relation
        assert!(rb1 == rb1);
        assert!(rb2 == rb2);
    }

    #[test]
    fn hash_equality() {
        // generate two queues with same content
        // but different buffer alignment
        let rb1 = {
            let mut rb1: Queue<i32, U4> = Queue::new();
            rb1.enqueue(0).unwrap();
            rb1.enqueue(0).unwrap();
            rb1.dequeue().unwrap();
            rb1.enqueue(0).unwrap();
            rb1
        };
        let rb2 = {
            let mut rb2: Queue<i32, U4> = Queue::new();
            rb2.enqueue(0).unwrap();
            rb2.enqueue(0).unwrap();
            rb2
        };
        let hash1 = {
            let mut hasher1 = hash32::FnvHasher::default();
            hash32::Hash::hash(&rb1, &mut hasher1);
            let hash1 = hasher1.finish();
            hash1
        };
        let hash2 = {
            let mut hasher2 = hash32::FnvHasher::default();
            hash32::Hash::hash(&rb2, &mut hasher2);
            let hash2 = hasher2.finish();
            hash2
        };
        assert_eq!(hash1, hash2);
    }

}

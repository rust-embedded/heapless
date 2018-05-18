//! Ring buffer

use core::cell::UnsafeCell;
use core::ops::Add;
use core::{intrinsics, ptr};

use generic_array::typenum::{Sum, U1, Unsigned};
use generic_array::{ArrayLength, GenericArray};

pub use self::spsc::{Consumer, Producer};
use __core::mem::{self, ManuallyDrop};

mod spsc;

/// Types that can be used as `RingBuffer` indices: `u8`, `u16` and `usize
///
/// Do not implement this trait yourself
pub unsafe trait Uxx: Into<usize> + Send {
    #[doc(hidden)]
    fn truncate(x: usize) -> Self;
}

unsafe impl Uxx for u8 {
    fn truncate(x: usize) -> Self {
        let max = ::core::u8::MAX;
        if x >= usize::from(max) {
            max - 1
        } else {
            x as u8
        }
    }
}

unsafe impl Uxx for u16 {
    fn truncate(x: usize) -> Self {
        let max = ::core::u16::MAX;
        if x >= usize::from(max) {
            max - 1
        } else {
            x as u16
        }
    }
}

unsafe impl Uxx for usize {
    fn truncate(x: usize) -> Self {
        x
    }
}

// Atomic{U8,U16, Usize} with no CAS operations that works on targets that have "no atomic support"
// according to their specification
struct Atomic<U>
where
    U: Uxx,
{
    v: UnsafeCell<U>,
}

impl<U> Atomic<U>
where
    U: Uxx,
{
    const_fn!(
        const fn new(v: U) -> Atomic<U> {
            Atomic {
                v: UnsafeCell::new(v),
            }
        }
    );

    fn get_mut(&mut self) -> &mut U {
        unsafe { &mut *self.v.get() }
    }

    fn load_acquire(&self) -> U {
        unsafe { intrinsics::atomic_load_acq(self.v.get()) }
    }

    fn load_relaxed(&self) -> U {
        unsafe { intrinsics::atomic_load_relaxed(self.v.get()) }
    }

    fn store_release(&self, val: U) {
        unsafe { intrinsics::atomic_store_rel(self.v.get(), val) }
    }
}

/// A statically allocated ring buffer with a capacity of `N`
///
/// By default `RingBuffer` will use `usize` integers to hold the indices to its head and tail. For
/// small ring buffers `usize` may be overkill. However, `RingBuffer`'s index type is generic and
/// can be changed to `u8` or `u16` to reduce its footprint. The easiest to construct a `RingBuffer`
/// with a smaller index type is to use the [`u8`] and [`u16`] constructors.
///
/// [`u8`]: struct.RingBuffer.html#method.u8
/// [`u16`]: struct.RingBuffer.html#method.u16
///
/// # Examples
///
/// ```
/// use heapless::RingBuffer;
/// use heapless::consts::*;
///
/// let mut rb: RingBuffer<u8, U3> = RingBuffer::new();
///
/// assert!(rb.enqueue(0).is_ok());
/// assert!(rb.enqueue(1).is_ok());
/// assert!(rb.enqueue(2).is_ok());
/// assert!(rb.enqueue(3).is_err()); // full
///
/// assert_eq!(rb.dequeue(), Some(0));
/// ```
///
/// ### Single producer single consumer mode
///
/// ```
/// use heapless::RingBuffer;
/// use heapless::consts::*;
///
/// static mut RB: RingBuffer<Event, U4> = RingBuffer::new();
///
/// enum Event { A, B }
///
/// fn main() {
///     // NOTE(unsafe) beware of aliasing the `consumer` end point
///     let mut consumer = unsafe { RB.split().1 };
///
///     loop {
///         // `dequeue` is a lockless operation
///         match consumer.dequeue() {
///             Some(Event::A) => { /* .. */ },
///             Some(Event::B) => { /* .. */ },
///             None => { /* sleep */},
///         }
/// #       break
///     }
/// }
///
/// // this is a different execution context that can preempt `main`
/// fn interrupt_handler() {
///     // NOTE(unsafe) beware of aliasing the `producer` end point
///     let mut producer = unsafe { RB.split().0 };
/// #   let condition = true;
///
///     // ..
///
///     if condition {
///         producer.enqueue(Event::A).ok().unwrap();
///     } else {
///         producer.enqueue(Event::B).ok().unwrap();
///     }
///
///     // ..
/// }
/// ```
pub struct RingBuffer<T, N, U = usize>
where
    N: Add<U1> + Unsigned,
    Sum<N, U1>: ArrayLength<T>,
    U: Uxx,
{
    // this is from where we dequeue items
    head: Atomic<U>,

    // this is where we enqueue new items
    tail: Atomic<U>,

    buffer: ManuallyDrop<GenericArray<T, Sum<N, U1>>>,
}

impl<T, N, U> RingBuffer<T, N, U>
where
    N: Add<U1> + Unsigned,
    Sum<N, U1>: ArrayLength<T>,
    U: Uxx,
{
    /// Returns the maximum number of elements the ring buffer can hold
    pub fn capacity(&self) -> U {
        U::truncate(N::to_usize())
    }

    /// Returns `true` if the ring buffer has a length of 0
    pub fn is_empty(&self) -> bool {
        self.len_usize() == 0
    }

    /// Iterates from the front of the queue to the back
    pub fn iter(&self) -> Iter<T, N, U> {
        Iter {
            rb: self,
            index: 0,
            len: self.len_usize(),
        }
    }

    /// Returns an iterator that allows modifying each value.
    pub fn iter_mut(&mut self) -> IterMut<T, N, U> {
        let len = self.len_usize();
        IterMut {
            rb: self,
            index: 0,
            len,
        }
    }

    fn len_usize(&self) -> usize {
        let head = self.head.load_relaxed().into();
        let tail = self.tail.load_relaxed().into();

        if head > tail {
            head - tail
        } else {
            tail - head
        }
    }
}

impl<T, N, U> Drop for RingBuffer<T, N, U>
where
    N: Add<U1> + Unsigned,
    Sum<N, U1>: ArrayLength<T>,
    U: Uxx,
{
    fn drop(&mut self) {
        for item in self {
            unsafe {
                ptr::drop_in_place(item);
            }
        }
    }
}

impl<'a, T, N, U> IntoIterator for &'a RingBuffer<T, N, U>
where
    N: Add<U1> + Unsigned,
    Sum<N, U1>: ArrayLength<T>,
    U: Uxx,
{
    type Item = &'a T;
    type IntoIter = Iter<'a, T, N, U>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T, N, U> IntoIterator for &'a mut RingBuffer<T, N, U>
where
    N: Add<U1> + Unsigned,
    Sum<N, U1>: ArrayLength<T>,
    U: Uxx,
{
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T, N, U>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

macro_rules! impl_ {
    ($uxx:ident) => {
        impl<T, N> RingBuffer<T, N, $uxx>
        where
            N: Add<U1> + Unsigned,
            Sum<N, U1>: ArrayLength<T>,
        {
            /// Creates an empty ring buffer with a fixed capacity of `N`
            const_fn!(
                pub const fn $uxx() -> Self {
                    RingBuffer {
                        buffer: ManuallyDrop::new(unsafe { mem::uninitialized() }),
                        head: Atomic::new(0),
                        tail: Atomic::new(0),
                    }
                }
            );

            /// Returns the item in the front of the queue, or `None` if the queue is empty
            pub fn dequeue(&mut self) -> Option<T> {
                let n = self.capacity() + 1;

                let head = self.head.get_mut();
                let tail = self.tail.get_mut();

                let buffer = self.buffer.as_slice();

                if *head != *tail {
                    let item = unsafe { ptr::read(buffer.get_unchecked(usize::from(*head))) };
                    *head = (*head + 1) % n;
                    Some(item)
                } else {
                    None
                }
            }

            /// Adds an `item` to the end of the queue
            ///
            /// Returns back the `item` if the queue is full
            pub fn enqueue(&mut self, item: T) -> Result<(), T> {
                let n = self.capacity() + 1;

                let head = *self.head.get_mut();
                let tail = *self.tail.get_mut();

                let next_tail = (tail + 1) % n;
                if next_tail != head {
                    self.enqueue_unchecked(item);
                    Ok(())
                } else {
                    Err(item)
                }
            }

            /// Adds an `item` to the end of the queue, without checking if it's full
            ///
            /// **WARNING** If the queue is full this operation will make the queue appear empty to
            /// the `Consumer`, thus *leaking* (destructors won't run) all the elements that were in
            /// the queue.
            pub fn enqueue_unchecked(&mut self, item: T) {
                let n = self.capacity() + 1;

                let tail = self.tail.get_mut();

                let buffer = self.buffer.as_mut_slice();

                let next_tail = (*tail + 1) % n;
                // NOTE(ptr::write) the memory slot that we are about to write to is
                // uninitialized. We use `ptr::write` to avoid running `T`'s destructor on the
                // uninitialized memory
                unsafe { ptr::write(buffer.get_unchecked_mut(usize::from(*tail)), item) }
                *tail = next_tail;
            }

            /// Returns the number of elements in the queue
            pub fn len(&self) -> $uxx {
                let head = self.head.load_relaxed();
                let tail = self.tail.load_relaxed();

                if head > tail {
                    head - tail
                } else {
                    tail - head
                }
            }
        }
    };
}

impl<T, N> RingBuffer<T, N, usize>
where
    N: Add<U1> + Unsigned,
    Sum<N, U1>: ArrayLength<T>,
{
    /// Alias for [`RingBuffer::usize`](struct.RingBuffer.html#method.usize)
    const_fn!(
        pub const fn new() -> Self {
            RingBuffer::usize()
        }
    );
}

impl_!(u8);
impl_!(u16);
impl_!(usize);

/// An iterator over a ring buffer items
pub struct Iter<'a, T, N, U>
where
    N: Add<U1> + Unsigned + 'a,
    Sum<N, U1>: ArrayLength<T>,
    T: 'a,
    U: 'a + Uxx,
{
    rb: &'a RingBuffer<T, N, U>,
    index: usize,
    len: usize,
}

/// A mutable iterator over a ring buffer items
pub struct IterMut<'a, T, N, U>
where
    N: Add<U1> + Unsigned + 'a,
    Sum<N, U1>: ArrayLength<T>,
    T: 'a,
    U: 'a + Uxx,
{
    rb: &'a mut RingBuffer<T, N, U>,
    index: usize,
    len: usize,
}

macro_rules! iterator {
    (struct $name:ident -> $elem:ty, $ptr:ty, $asref:ident, $asptr:ident, $mkref:ident) => {
        impl<'a, T, N, U> Iterator for $name<'a, T, N, U>
        where
            N: Add<U1> + Unsigned,
            Sum<N, U1>: ArrayLength<T>,
            T: 'a,
            U: 'a + Uxx,
        {
            type Item = $elem;

            fn next(&mut self) -> Option<$elem> {
                if self.index < self.len {
                    let head = self.rb.head.load_relaxed().into();

                    let capacity = self.rb.capacity().into() + 1;
                    let buffer = self.rb.buffer.$asref();
                    let ptr: $ptr = buffer.$asptr();
                    let i = (head + self.index) % capacity;
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

iterator!(struct Iter -> &'a T, *const T, as_slice, as_ptr, make_ref);
iterator!(struct IterMut -> &'a mut T, *mut T, as_mut_slice, as_mut_ptr, make_ref_mut);

#[cfg(test)]
mod tests {
    use consts::*;
    use RingBuffer;

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
            let mut v: RingBuffer<Droppable, U4> = RingBuffer::new();
            v.enqueue(Droppable::new()).ok().unwrap();
            v.enqueue(Droppable::new()).ok().unwrap();
            v.dequeue().unwrap();
        }

        assert_eq!(unsafe { COUNT }, 0);

        {
            let mut v: RingBuffer<Droppable, U4> = RingBuffer::new();
            v.enqueue(Droppable::new()).ok().unwrap();
            v.enqueue(Droppable::new()).ok().unwrap();
        }

        assert_eq!(unsafe { COUNT }, 0);
    }

    #[test]
    fn full() {
        let mut rb: RingBuffer<i32, U3> = RingBuffer::new();

        rb.enqueue(0).unwrap();
        rb.enqueue(1).unwrap();
        rb.enqueue(2).unwrap();

        assert!(rb.enqueue(3).is_err());
    }

    #[test]
    fn iter() {
        let mut rb: RingBuffer<i32, U4> = RingBuffer::new();

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
        let mut rb: RingBuffer<i32, U4> = RingBuffer::new();

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
        let mut rb: RingBuffer<i32, U4> = RingBuffer::new();

        assert_eq!(rb.dequeue(), None);

        rb.enqueue(0).unwrap();

        assert_eq!(rb.dequeue(), Some(0));

        assert_eq!(rb.dequeue(), None);
    }

    #[test]
    fn u8() {
        let mut rb: RingBuffer<u8, U256, _> = RingBuffer::u8();

        for _ in 0..254 {
            rb.enqueue(0).unwrap();
        }

        assert!(rb.enqueue(0).is_err());
    }

    #[test]
    fn wrap_around() {
        let mut rb: RingBuffer<i32, U3> = RingBuffer::new();

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
}

//! Ring buffer

use core::cell::UnsafeCell;
use core::ptr;

use generic_array::{ArrayLength, GenericArray};

pub use self::split::{Consumer, Producer};
use __core::mem::MaybeUninit;
use sealed;

mod split;

// Atomic{U8,U16, Usize} with no CAS operations that works on targets that have "no atomic support"
// according to their specification
struct Atomic<U>
where
    U: sealed::Uxx,
{
    v: UnsafeCell<U>,
}

impl<U> Atomic<U>
where
    U: sealed::Uxx,
{
    const_fn! {
        const fn new(v: U) -> Atomic<U> {
            Atomic {
                v: UnsafeCell::new(v),
            }
        }
    }

    fn get_mut(&mut self) -> &mut U {
        unsafe { &mut *self.v.get() }
    }

    fn load_acquire(&self) -> U {
        U::load_acquire(self.v.get())
    }

    fn load_relaxed(&self) -> U {
        U::load_relaxed(self.v.get())
    }

    fn store_release(&self, val: U) {
        U::store_release(self.v.get(), val)
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
/// # Examples
///
/// ```
/// use heapless::spsc::Queue;
/// use heapless::consts::*;
///
/// let mut rb: Queue<u8, U4> = Queue::new();
///
/// assert!(rb.enqueue(0).is_ok());
/// assert!(rb.enqueue(1).is_ok());
/// assert!(rb.enqueue(2).is_ok());
/// assert!(rb.enqueue(3).is_ok());
/// assert!(rb.enqueue(4).is_err()); // full
///
/// assert_eq!(rb.dequeue(), Some(0));
/// ```
///
/// ### Single producer single consumer mode
///
/// ```
/// use heapless::spsc::Queue;
/// use heapless::consts::*;
///
/// // static mut RB: Queue<Event, U4> = Queue::new(); // requires feature `const-fn`
///
/// static mut RB: Option<Queue<Event, U4>>  = None;
///
/// enum Event { A, B }
///
/// fn main() {
///     unsafe { RB = Some(Queue::new()) };
///     // NOTE(unsafe) beware of aliasing the `consumer` end point
///     let mut consumer = unsafe { RB.as_mut().unwrap().split().1 };
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
///     let mut producer = unsafe { RB.as_mut().unwrap().split().0 };
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
pub struct Queue<T, N, U = usize>
where
    N: ArrayLength<T>,
    U: sealed::Uxx,
{
    // this is from where we dequeue items
    head: Atomic<U>,

    // this is where we enqueue new items
    tail: Atomic<U>,

    buffer: MaybeUninit<GenericArray<T, N>>,
}

impl<T, N, U> Queue<T, N, U>
where
    N: ArrayLength<T>,
    U: sealed::Uxx,
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

        tail.wrapping_sub(head)
    }
}

impl<T, N, U> Drop for Queue<T, N, U>
where
    N: ArrayLength<T>,
    U: sealed::Uxx,
{
    fn drop(&mut self) {
        for item in self {
            unsafe {
                ptr::drop_in_place(item);
            }
        }
    }
}

impl<'a, T, N, U> IntoIterator for &'a Queue<T, N, U>
where
    N: ArrayLength<T>,
    U: sealed::Uxx,
{
    type Item = &'a T;
    type IntoIter = Iter<'a, T, N, U>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T, N, U> IntoIterator for &'a mut Queue<T, N, U>
where
    N: ArrayLength<T>,
    U: sealed::Uxx,
{
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T, N, U>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

macro_rules! impl_ {
    ($uxx:ident) => {
        impl<T, N> Queue<T, N, $uxx>
        where
            N: ArrayLength<T>,
        {
            const_fn! {
                /// Creates an empty queue with a fixed capacity of `N`
                pub const fn $uxx() -> Self {
                    Queue {
                        buffer: unsafe { MaybeUninit::uninitialized() },
                        head: Atomic::new(0),
                        tail: Atomic::new(0),
                    }
                }
            }

            /// Returns the item in the front of the queue, or `None` if the queue is empty
            pub fn dequeue(&mut self) -> Option<T> {
                let cap = self.capacity();

                let head = self.head.get_mut();
                let tail = self.tail.get_mut();

                let buffer = unsafe { self.buffer.get_ref() };

                if *head != *tail {
                    let item = unsafe { ptr::read(buffer.get_unchecked(usize::from(*head % cap))) };
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
                let head = *self.head.get_mut();
                let tail = *self.tail.get_mut();

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
                let tail = self.tail.get_mut();

                let buffer = self.buffer.get_mut();

                // NOTE(ptr::write) the memory slot that we are about to write to is
                // uninitialized. We use `ptr::write` to avoid running `T`'s destructor on the
                // uninitialized memory
                ptr::write(buffer.get_unchecked_mut(usize::from(*tail % cap)), item);
                *tail = tail.wrapping_add(1);
            }

            /// Returns the number of elements in the queue
            pub fn len(&self) -> $uxx {
                let head = self.head.load_relaxed();
                let tail = self.tail.load_relaxed();

                if head > tail {
                    tail.wrapping_sub(head)
                } else {
                    tail - head
                }
            }
        }
    };
}

impl<T, N> Queue<T, N, usize>
where
    N: ArrayLength<T>,
{
    const_fn! {
        /// Alias for [`spsc::Queue::usize`](struct.Queue.html#method.usize)
        pub const fn new() -> Self {
            Queue::usize()
        }
    }
}

#[cfg(feature = "smaller-atomics")]
impl_!(u8);
#[cfg(feature = "smaller-atomics")]
impl_!(u16);
impl_!(usize);

/// An iterator over the items of a queue
pub struct Iter<'a, T, N, U>
where
    N: ArrayLength<T> + 'a,
    T: 'a,
    U: 'a + sealed::Uxx,
{
    rb: &'a Queue<T, N, U>,
    index: usize,
    len: usize,
}

/// A mutable iterator over the items of a queue
pub struct IterMut<'a, T, N, U>
where
    N: ArrayLength<T> + 'a,
    T: 'a,
    U: 'a + sealed::Uxx,
{
    rb: &'a mut Queue<T, N, U>,
    index: usize,
    len: usize,
}

macro_rules! iterator {
    (struct $name:ident -> $elem:ty, $ptr:ty, $asref:ident, $asptr:ident, $mkref:ident) => {
        impl<'a, T, N, U> Iterator for $name<'a, T, N, U>
        where
            N: ArrayLength<T>,
            T: 'a,
            U: 'a + sealed::Uxx,
        {
            type Item = $elem;

            fn next(&mut self) -> Option<$elem> {
                if self.index < self.len {
                    let head = self.rb.head.load_relaxed().into();

                    let cap = self.rb.capacity().into();
                    let buffer = unsafe { self.rb.buffer.$asref() };
                    let ptr: $ptr = buffer.$asptr();
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

iterator!(struct Iter -> &'a T, *const T, get_ref, as_ptr, make_ref);
iterator!(struct IterMut -> &'a mut T, *mut T, get_mut, as_mut_ptr, make_ref_mut);

#[cfg(test)]
mod tests {
    use consts::*;
    use spsc::Queue;

    #[cfg(feature = "const-fn")]
    #[test]
    fn static_new() {
        static mut _Q: Queue<i32, U4> = Queue::new();
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
}

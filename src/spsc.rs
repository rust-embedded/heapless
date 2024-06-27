//! A fixed capacity Single Producer Single Consumer (SPSC) queue.
//!
//! Implementation based on <https://www.codeproject.com/Articles/43510/Lock-Free-Single-Producer-Single-Consumer-Circular>
//!
//! # Portability
//!
//! This module requires CAS atomic instructions which are not available on all architectures
//! (e.g.  ARMv6-M (`thumbv6m-none-eabi`) and MSP430 (`msp430-none-elf`)). These atomics can be
//! emulated however with [`portable-atomic`](https://crates.io/crates/portable-atomic), which is
//! enabled with the `cas` feature and is enabled by default for `thumbv6m-none-eabi` and `riscv32`
//! targets.
//!
//! # Examples
//!
//! - `Queue` can be used as a plain queue
//!
//! ```
//! use heapless::spsc::Queue;
//!
//! let mut rb: Queue<u8, 4> = Queue::new();
//!
//! assert!(rb.enqueue(0).is_ok());
//! assert!(rb.enqueue(1).is_ok());
//! assert!(rb.enqueue(2).is_ok());
//! assert!(rb.enqueue(3).is_err()); // full
//!
//! assert_eq!(rb.dequeue(), Some(0));
//! ```
//!
//! - `Queue` can be `split` and then be used in Single Producer Single Consumer mode.
//!
//! "no alloc" applications can create a `&'static mut` reference to a `Queue` -- using a static
//! variable -- and then `split` it: this consumes the static reference. The resulting `Consumer`
//! and `Producer` can then be moved into different execution contexts (threads, interrupt handlers,
//! etc.)
//!
//! ```
//! use heapless::spsc::{Producer, Queue};
//!
//! enum Event {
//!     A,
//!     B,
//! }
//!
//! fn main() {
//!     let queue: &'static mut Queue<Event, 4> = {
//!         static mut Q: Queue<Event, 4> = Queue::new();
//!         unsafe { &mut Q }
//!     };
//!
//!     let (producer, mut consumer) = queue.split();
//!
//!     // `producer` can be moved into `interrupt_handler` using a static mutex or the mechanism
//!     // provided by the concurrency framework you are using (e.g. a resource in RTIC)
//!
//!     loop {
//!         match consumer.dequeue() {
//!             Some(Event::A) => { /* .. */ }
//!             Some(Event::B) => { /* .. */ }
//!             None => { /* sleep */ }
//!         }
//! #       break
//!     }
//! }
//!
//! // this is a different execution context that can preempt `main`
//! fn interrupt_handler(producer: &mut Producer<'static, Event, 4>) {
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

#[cfg(not(feature = "portable-atomic"))]
use core::sync::atomic;
#[cfg(feature = "portable-atomic")]
use portable_atomic as atomic;

use atomic::{AtomicUsize, Ordering};

mod private {
    use super::*;

    /// <div class="warn">This is private API and should not be used</div>
    pub struct QueueInner<B: ?Sized + QueueBuffer> {
        // this is from where we dequeue items
        pub(crate) head: AtomicUsize,

        // this is where we enqueue new items
        pub(crate) tail: AtomicUsize,

        pub(crate) buffer: B,
    }

    pub trait QueueBuffer {
        type T;
        fn as_view(this: &QueueInner<Self>) -> &QueueView<Self::T>;
        fn as_mut_view(this: &mut QueueInner<Self>) -> &mut QueueView<Self::T>;
    }
}

// Workaround https://github.com/rust-lang/rust/issues/119015. This is required so that the methods on `Queue` and `QueueView` are properly documented.
// cfg(doc) prevents `QueueInner` being part of the public API.
// doc(hidden) prevents the `pub use vec::VecInner` from being visible in the documentation.
#[cfg(doc)]
#[doc(hidden)]
pub use private::QueueInner as _;

/// A statically allocated single producer single consumer queue with a capacity of `N - 1` elements
///
/// *IMPORTANT*: To get better performance use a value for `N` that is a power of 2 (e.g. `16`, `32`,
/// etc.).
pub type Queue<T, const N: usize> = private::QueueInner<[UnsafeCell<MaybeUninit<T>>; N]>;

/// A statically allocated single producer single consumer queue with dynamic capacity
pub type QueueView<T> = private::QueueInner<[UnsafeCell<MaybeUninit<T>>]>;

impl<T, const N: usize> private::QueueBuffer for [UnsafeCell<MaybeUninit<T>>; N] {
    type T = T;

    fn as_view(this: &private::QueueInner<Self>) -> &QueueView<Self::T> {
        this
    }
    fn as_mut_view(this: &mut private::QueueInner<Self>) -> &mut QueueView<Self::T> {
        this
    }
}

impl<T> private::QueueBuffer for [UnsafeCell<MaybeUninit<T>>] {
    type T = T;

    fn as_view(this: &private::QueueInner<Self>) -> &QueueView<Self::T> {
        this
    }
    fn as_mut_view(this: &mut private::QueueInner<Self>) -> &mut QueueView<Self::T> {
        this
    }
}

impl<T, const N: usize> Queue<T, N> {
    const INIT: UnsafeCell<MaybeUninit<T>> = UnsafeCell::new(MaybeUninit::uninit());

    /// Get a reference to the `Queue`, erasing the `N` const-generic.
    ///
    /// ```
    /// use heapless::spsc::{Queue, QueueView};
    ///
    /// let rb: Queue<u8, 4> = Queue::new();
    /// let rb_view: &QueueView<u8> = rb.as_view();
    /// ```
    /// It is often preferable to do the same through type coerction, since `Queue<T, N>` implements `Unsize<QueueView<T>>`:
    ///
    /// ```
    /// use heapless::spsc::{Queue, QueueView};
    ///
    /// let rb: Queue<u8, 4> = Queue::new();
    /// let rb_view: &QueueView<u8> = &rb;
    /// ```
    pub fn as_view(&self) -> &QueueView<T> {
        self
    }

    /// Get a mutable reference to the `Queue`, erasing the `N` const-generic.
    ///
    /// ```
    /// use heapless::spsc::{Queue, QueueView};
    ///
    /// let mut rb: Queue<u8, 4> = Queue::new();
    /// let rb_view: &mut QueueView<u8> = rb.as_mut_view();
    /// ```
    /// It is often preferable to do the same through type coerction, since `Queue<T, N>` implements `Unsize<QueueView<T>>`:
    ///
    /// ```
    /// use heapless::spsc::{Queue, QueueView};
    ///
    /// let mut rb: Queue<u8, 4> = Queue::new();
    /// let rb_view: &mut QueueView<u8> = &mut rb;
    /// ```
    pub fn as_mut_view(&mut self) -> &mut QueueView<T> {
        self
    }

    /// Creates an empty queue with a fixed capacity of `N - 1`
    pub const fn new() -> Self {
        // Const assert N > 1
        crate::sealed::greater_than_1::<N>();

        Queue {
            head: AtomicUsize::new(0),
            tail: AtomicUsize::new(0),
            buffer: [Self::INIT; N],
        }
    }

    /// Returns the maximum number of elements the queue can hold
    #[inline]
    pub const fn capacity(&self) -> usize {
        N - 1
    }

    /// Returns the number of elements in the queue
    #[inline]
    pub fn len(&self) -> usize {
        self.as_view().len()
    }

    /// Returns `true` if the queue is empty
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.as_view().is_empty()
    }

    /// Returns `true` if the queue is full
    #[inline]
    pub fn is_full(&self) -> bool {
        self.as_view().is_full()
    }

    /// Iterates from the front of the queue to the back
    pub fn iter(&self) -> Iter<'_, T, N> {
        Iter {
            inner: self.as_view().iter(),
            phantom: PhantomData,
        }
    }

    /// Returns an iterator that allows modifying each value
    pub fn iter_mut(&mut self) -> IterMut<'_, T, N> {
        IterMut {
            inner: self.as_mut_view().iter_mut(),
            phantom: PhantomData,
        }
    }

    /// Adds an `item` to the end of the queue
    ///
    /// Returns back the `item` if the queue is full
    #[inline]
    pub fn enqueue(&mut self, val: T) -> Result<(), T> {
        self.as_mut_view().enqueue(val)
    }

    /// Returns the item in the front of the queue, or `None` if the queue is empty
    #[inline]
    pub fn dequeue(&mut self) -> Option<T> {
        self.as_mut_view().dequeue()
    }

    /// Returns a reference to the item in the front of the queue without dequeuing, or
    /// `None` if the queue is empty.
    ///
    /// # Examples
    /// ```
    /// use heapless::spsc::Queue;
    ///
    /// let mut queue: Queue<u8, 235> = Queue::new();
    /// let (mut producer, mut consumer) = queue.split();
    /// assert_eq!(None, consumer.peek());
    /// producer.enqueue(1);
    /// assert_eq!(Some(&1), consumer.peek());
    /// assert_eq!(Some(1), consumer.dequeue());
    /// assert_eq!(None, consumer.peek());
    /// ```
    pub fn peek(&self) -> Option<&T> {
        self.as_view().peek()
    }

    /// Adds an `item` to the end of the queue, without checking if it's full
    ///
    /// # Safety
    ///
    /// If the queue is full this operation will leak a value (T's destructor won't run on
    /// the value that got overwritten by `item`), *and* will allow the `dequeue` operation
    /// to create a copy of `item`, which could result in `T`'s destructor running on `item`
    /// twice.
    pub unsafe fn enqueue_unchecked(&mut self, val: T) {
        self.as_mut_view().inner_enqueue_unchecked(val)
    }

    /// Returns the item in the front of the queue, without checking if there is something in the
    /// queue
    ///
    /// # Safety
    ///
    /// If the queue is empty this operation will return uninitialized memory.
    pub unsafe fn dequeue_unchecked(&mut self) -> T {
        self.as_mut_view().dequeue_unchecked()
    }

    /// Splits a queue into producer and consumer endpoints
    pub fn split(&mut self) -> (Producer<'_, T, N>, Consumer<'_, T, N>) {
        let (producer, consumer) = self.as_mut_view().split();
        (
            Producer {
                inner: producer,
                phantom: PhantomData,
            },
            Consumer {
                inner: consumer,
                phantom: PhantomData,
            },
        )
    }
}

impl<T> QueueView<T> {
    #[inline]
    fn increment(&self, val: usize) -> usize {
        (val + 1) % self.n()
    }

    /// Returns the maximum number of elements the queue can hold
    #[inline]
    pub const fn capacity(&self) -> usize {
        self.n() - 1
    }

    #[inline]
    const fn n(&self) -> usize {
        self.buffer.len()
    }

    /// Returns the number of elements in the queue
    #[inline]
    pub fn len(&self) -> usize {
        let current_head = self.head.load(Ordering::Relaxed);
        let current_tail = self.tail.load(Ordering::Relaxed);

        current_tail
            .wrapping_sub(current_head)
            .wrapping_add(self.n())
            % self.n()
    }

    /// Returns `true` if the queue is empty
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.head.load(Ordering::Relaxed) == self.tail.load(Ordering::Relaxed)
    }

    /// Returns `true` if the queue is full
    #[inline]
    pub fn is_full(&self) -> bool {
        self.increment(self.tail.load(Ordering::Relaxed)) == self.head.load(Ordering::Relaxed)
    }

    /// Iterates from the front of the queue to the back
    pub fn iter(&self) -> IterView<'_, T> {
        IterView {
            rb: self,
            index: 0,
            len: self.len(),
        }
    }

    /// Returns an iterator that allows modifying each value
    pub fn iter_mut(&mut self) -> IterMutView<'_, T> {
        let len = self.len();
        IterMutView {
            rb: self,
            index: 0,
            len,
        }
    }

    /// Adds an `item` to the end of the queue
    ///
    /// Returns back the `item` if the queue is full
    #[inline]
    pub fn enqueue(&mut self, val: T) -> Result<(), T> {
        unsafe { self.inner_enqueue(val) }
    }

    /// Returns the item in the front of the queue, or `None` if the queue is empty
    #[inline]
    pub fn dequeue(&mut self) -> Option<T> {
        unsafe { self.inner_dequeue() }
    }

    /// Returns a reference to the item in the front of the queue without dequeuing, or
    /// `None` if the queue is empty.
    ///
    /// # Examples
    /// ```
    /// use heapless::spsc::{Queue, QueueView};
    ///
    /// let mut queue: Queue<u8, 235> = Queue::new();
    /// let queue_view: &mut QueueView<u8> = &mut queue;
    /// let (mut producer, mut consumer) = queue_view.split();
    /// assert_eq!(None, consumer.peek());
    /// producer.enqueue(1);
    /// assert_eq!(Some(&1), consumer.peek());
    /// assert_eq!(Some(1), consumer.dequeue());
    /// assert_eq!(None, consumer.peek());
    /// ```
    pub fn peek(&self) -> Option<&T> {
        if !self.is_empty() {
            let head = self.head.load(Ordering::Relaxed);
            Some(unsafe { &*(self.buffer.get_unchecked(head).get() as *const T) })
        } else {
            None
        }
    }

    // The memory for enqueueing is "owned" by the tail pointer.
    // NOTE: This internal function uses internal mutability to allow the [`ProducerView`] to enqueue
    // items without doing pointer arithmetic and accessing internal fields of this type.
    unsafe fn inner_enqueue(&self, val: T) -> Result<(), T> {
        let current_tail = self.tail.load(Ordering::Relaxed);
        let next_tail = self.increment(current_tail);

        if next_tail != self.head.load(Ordering::Acquire) {
            (self.buffer.get_unchecked(current_tail).get()).write(MaybeUninit::new(val));
            self.tail.store(next_tail, Ordering::Release);

            Ok(())
        } else {
            Err(val)
        }
    }

    // The memory for enqueueing is "owned" by the tail pointer.
    // NOTE: This internal function uses internal mutability to allow the [`ProducerView`] to enqueue
    // items without doing pointer arithmetic and accessing internal fields of this type.
    unsafe fn inner_enqueue_unchecked(&self, val: T) {
        let current_tail = self.tail.load(Ordering::Relaxed);

        (self.buffer.get_unchecked(current_tail).get()).write(MaybeUninit::new(val));
        self.tail
            .store(self.increment(current_tail), Ordering::Release);
    }

    /// Adds an `item` to the end of the queue, without checking if it's full
    ///
    /// # Safety
    ///
    /// If the queue is full this operation will leak a value (T's destructor won't run on
    /// the value that got overwritten by `item`), *and* will allow the `dequeue` operation
    /// to create a copy of `item`, which could result in `T`'s destructor running on `item`
    /// twice.
    pub unsafe fn enqueue_unchecked(&mut self, val: T) {
        self.inner_enqueue_unchecked(val)
    }

    // The memory for dequeuing is "owned" by the head pointer,.
    // NOTE: This internal function uses internal mutability to allow the [`ConsumerView`] to dequeue
    // items without doing pointer arithmetic and accessing internal fields of this type.
    unsafe fn inner_dequeue(&self) -> Option<T> {
        let current_head = self.head.load(Ordering::Relaxed);

        if current_head == self.tail.load(Ordering::Acquire) {
            None
        } else {
            let v = (self.buffer.get_unchecked(current_head).get() as *const T).read();

            self.head
                .store(self.increment(current_head), Ordering::Release);

            Some(v)
        }
    }

    // The memory for dequeuing is "owned" by the head pointer,.
    // NOTE: This internal function uses internal mutability to allow the [`ConsumerView`] to dequeue
    // items without doing pointer arithmetic and accessing internal fields of this type.
    unsafe fn inner_dequeue_unchecked(&self) -> T {
        let current_head = self.head.load(Ordering::Relaxed);
        let v = (self.buffer.get_unchecked(current_head).get() as *const T).read();

        self.head
            .store(self.increment(current_head), Ordering::Release);

        v
    }

    /// Returns the item in the front of the queue, without checking if there is something in the
    /// queue
    ///
    /// # Safety
    ///
    /// If the queue is empty this operation will return uninitialized memory.
    pub unsafe fn dequeue_unchecked(&mut self) -> T {
        self.inner_dequeue_unchecked()
    }

    /// Splits a queue into producer and consumer endpoints
    pub fn split(&mut self) -> (ProducerView<'_, T>, ConsumerView<'_, T>) {
        (ProducerView { rb: self }, ConsumerView { rb: self })
    }
}

impl<T, const N: usize> Default for Queue<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const N: usize> Clone for Queue<T, N>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        let mut new: Queue<T, N> = Queue::new();

        for s in self.iter() {
            unsafe {
                // NOTE(unsafe) new.capacity() == self.capacity() >= self.len()
                // no overflow possible
                new.enqueue_unchecked(s.clone());
            }
        }

        new
    }
}

impl<T, const N: usize, const N2: usize> PartialEq<Queue<T, N2>> for Queue<T, N>
where
    T: PartialEq,
{
    fn eq(&self, other: &Queue<T, N2>) -> bool {
        self.as_view().eq(other.as_view())
    }
}

impl<T, const N: usize> Eq for Queue<T, N> where T: Eq {}

impl<T> PartialEq<QueueView<T>> for QueueView<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &QueueView<T>) -> bool {
        self.len() == other.len() && self.iter().zip(other.iter()).all(|(v1, v2)| v1 == v2)
    }
}

impl<T, const N: usize> PartialEq<Queue<T, N>> for QueueView<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Queue<T, N>) -> bool {
        self.eq(other.as_view())
    }
}

impl<T, const N: usize> PartialEq<QueueView<T>> for Queue<T, N>
where
    T: PartialEq,
{
    fn eq(&self, other: &QueueView<T>) -> bool {
        self.as_view().eq(other)
    }
}

impl<T> Eq for QueueView<T> where T: Eq {}

/// An iterator over the items of a queue
pub struct IterView<'a, T> {
    rb: &'a QueueView<T>,
    index: usize,
    len: usize,
}

impl<'a, T> Clone for IterView<'a, T> {
    fn clone(&self) -> Self {
        Self {
            rb: self.rb,
            index: self.index,
            len: self.len,
        }
    }
}

/// A mutable iterator over the items of a queue
pub struct IterMutView<'a, T> {
    rb: &'a mut QueueView<T>,
    index: usize,
    len: usize,
}

impl<'a, T> Iterator for IterView<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.len {
            let head = self.rb.head.load(Ordering::Relaxed);

            let i = (head + self.index) % self.rb.n();
            self.index += 1;

            Some(unsafe { &*(self.rb.buffer.get_unchecked(i).get() as *const T) })
        } else {
            None
        }
    }
}

impl<'a, T> DoubleEndedIterator for IterView<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index < self.len {
            let head = self.rb.head.load(Ordering::Relaxed);

            // self.len > 0, since it's larger than self.index > 0
            let i = (head + self.len - 1) % self.rb.n();
            self.len -= 1;
            Some(unsafe { &*(self.rb.buffer.get_unchecked(i).get() as *const T) })
        } else {
            None
        }
    }
}

impl<'a, T> DoubleEndedIterator for IterMutView<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index < self.len {
            let head = self.rb.head.load(Ordering::Relaxed);

            // self.len > 0, since it's larger than self.index > 0
            let i = (head + self.len - 1) % self.rb.n();
            self.len -= 1;
            Some(unsafe { &mut *(self.rb.buffer.get_unchecked(i).get() as *mut T) })
        } else {
            None
        }
    }
}

impl<'a, T> Iterator for IterMutView<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.len {
            let head = self.rb.head.load(Ordering::Relaxed);

            let i = (head + self.index) % self.rb.n();
            self.index += 1;

            Some(unsafe { &mut *(self.rb.buffer.get_unchecked(i).get() as *mut T) })
        } else {
            None
        }
    }
}

/// A mutable iterator over the items of a queue
pub struct Iter<'a, T, const N: usize> {
    inner: IterView<'a, T>,
    /// PhantomData to keep the `N` const generic and avoid a breaking change
    phantom: PhantomData<[T; N]>,
}

impl<'a, T, const N: usize> Clone for Iter<'a, T, N> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            phantom: PhantomData,
        }
    }
}

/// A mutable iterator over the items of a queue
pub struct IterMut<'a, T, const N: usize> {
    inner: IterMutView<'a, T>,
    /// PhantomData to keep the `N` const generic and avoid a breaking change
    phantom: PhantomData<[T; N]>,
}

impl<'a, T, const N: usize> Iterator for Iter<'a, T, N> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<'a, T, const N: usize> Iterator for IterMut<'a, T, N> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<'a, T, const N: usize> DoubleEndedIterator for Iter<'a, T, N> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl<'a, T, const N: usize> DoubleEndedIterator for IterMut<'a, T, N> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl<B: ?Sized + private::QueueBuffer> Drop for private::QueueInner<B> {
    fn drop(&mut self) {
        let this = private::QueueBuffer::as_mut_view(self);
        for item in this {
            unsafe {
                ptr::drop_in_place(item);
            }
        }
    }
}

impl<T, const N: usize> fmt::Debug for Queue<T, N>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_view().fmt(f)
    }
}

impl<T> fmt::Debug for QueueView<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T, const N: usize> hash::Hash for Queue<T, N>
where
    T: hash::Hash,
{
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.as_view().hash(state)
    }
}

impl<T> hash::Hash for QueueView<T>
where
    T: hash::Hash,
{
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        // iterate over self in order
        for t in self.iter() {
            hash::Hash::hash(t, state);
        }
    }
}

impl<'a, T> IntoIterator for &'a QueueView<T> {
    type Item = &'a T;
    type IntoIter = IterView<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut QueueView<T> {
    type Item = &'a mut T;
    type IntoIter = IterMutView<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a Queue<T, N> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T, N>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a mut Queue<T, N> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T, N>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

/// A queue "consumer"; it can dequeue items from the queue
/// NOTE the consumer semantically owns the `head` pointer of the queue
pub struct Consumer<'a, T, const N: usize> {
    phantom: PhantomData<[T; N]>,
    inner: ConsumerView<'a, T>,
}

/// A queue "producer"; it can enqueue items into the queue
/// NOTE the producer semantically owns the `tail` pointer of the queue
pub struct Producer<'a, T, const N: usize> {
    phantom: PhantomData<[T; N]>,
    inner: ProducerView<'a, T>,
}

unsafe impl<'a, T, const N: usize> Send for Producer<'a, T, N> where T: Send {}

impl<'a, T, const N: usize> Consumer<'a, T, N> {
    /// Returns the item in the front of the queue, or `None` if the queue is empty
    #[inline]
    pub fn dequeue(&mut self) -> Option<T> {
        self.inner.dequeue()
    }

    /// Returns the item in the front of the queue, without checking if there are elements in the
    /// queue
    ///
    /// # Safety
    ///
    /// See [`Queue::dequeue_unchecked`]
    #[inline]
    pub unsafe fn dequeue_unchecked(&mut self) -> T {
        self.inner.dequeue_unchecked()
    }

    /// Returns if there are any items to dequeue. When this returns `true`, at least the
    /// first subsequent dequeue will succeed
    #[inline]
    pub fn ready(&self) -> bool {
        self.inner.ready()
    }

    /// Returns the number of elements in the queue
    #[inline]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns true if the queue is empty
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::spsc::Queue;
    ///
    /// let mut queue: Queue<u8, 235> = Queue::new();
    /// let (mut producer, mut consumer) = queue.split();
    /// assert!(consumer.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Returns the maximum number of elements the queue can hold
    #[inline]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Returns the item in the front of the queue without dequeuing, or `None` if the queue is
    /// empty
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::spsc::Queue;
    ///
    /// let mut queue: Queue<u8, 235> = Queue::new();
    /// let (mut producer, mut consumer) = queue.split();
    /// assert_eq!(None, consumer.peek());
    /// producer.enqueue(1);
    /// assert_eq!(Some(&1), consumer.peek());
    /// assert_eq!(Some(1), consumer.dequeue());
    /// assert_eq!(None, consumer.peek());
    /// ```
    #[inline]
    pub fn peek(&self) -> Option<&T> {
        self.inner.peek()
    }
}

impl<'a, T, const N: usize> Producer<'a, T, N> {
    /// Adds an `item` to the end of the queue, returns back the `item` if the queue is full
    #[inline]
    pub fn enqueue(&mut self, val: T) -> Result<(), T> {
        self.inner.enqueue(val)
    }

    /// Adds an `item` to the end of the queue, without checking if the queue is full
    ///
    /// # Safety
    ///
    /// See [`Queue::enqueue_unchecked`]
    #[inline]
    pub unsafe fn enqueue_unchecked(&mut self, val: T) {
        self.inner.enqueue_unchecked(val)
    }

    /// Returns if there is any space to enqueue a new item. When this returns true, at
    /// least the first subsequent enqueue will succeed.
    #[inline]
    pub fn ready(&self) -> bool {
        self.inner.ready()
    }

    /// Returns the number of elements in the queue
    #[inline]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns true if the queue is empty
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::spsc::Queue;
    ///
    /// let mut queue: Queue<u8, 235> = Queue::new();
    /// let (mut producer, mut consumer) = queue.split();
    /// assert!(producer.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Returns the maximum number of elements the queue can hold
    #[inline]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }
}

/// A queue "consumer"; it can dequeue items from the queue
/// NOTE the consumer semantically owns the `head` pointer of the queue
pub struct ConsumerView<'a, T> {
    rb: &'a QueueView<T>,
}

unsafe impl<'a, T> Send for ConsumerView<'a, T> where T: Send {}

/// A queue "producer"; it can enqueue items into the queue
/// NOTE the producer semantically owns the `tail` pointer of the queue
pub struct ProducerView<'a, T> {
    rb: &'a QueueView<T>,
}

unsafe impl<'a, T> Send for ProducerView<'a, T> where T: Send {}

impl<'a, T> ConsumerView<'a, T> {
    /// Returns the item in the front of the queue, or `None` if the queue is empty
    #[inline]
    pub fn dequeue(&mut self) -> Option<T> {
        unsafe { self.rb.inner_dequeue() }
    }

    /// Returns the item in the front of the queue, without checking if there are elements in the
    /// queue
    ///
    /// # Safety
    ///
    /// See [`Queue::dequeue_unchecked`]
    #[inline]
    pub unsafe fn dequeue_unchecked(&mut self) -> T {
        self.rb.inner_dequeue_unchecked()
    }

    /// Returns if there are any items to dequeue. When this returns `true`, at least the
    /// first subsequent dequeue will succeed
    #[inline]
    pub fn ready(&self) -> bool {
        !self.rb.is_empty()
    }

    /// Returns the number of elements in the queue
    #[inline]
    pub fn len(&self) -> usize {
        self.rb.len()
    }

    /// Returns true if the queue is empty
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::spsc::Queue;
    ///
    /// let mut queue: Queue<u8, 235> = Queue::new();
    /// let (mut producer, mut consumer) = queue.split();
    /// assert!(consumer.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the maximum number of elements the queue can hold
    #[inline]
    pub fn capacity(&self) -> usize {
        self.rb.capacity()
    }

    /// Returns the item in the front of the queue without dequeuing, or `None` if the queue is
    /// empty
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::spsc::Queue;
    ///
    /// let mut queue: Queue<u8, 235> = Queue::new();
    /// let (mut producer, mut consumer) = queue.split();
    /// assert_eq!(None, consumer.peek());
    /// producer.enqueue(1);
    /// assert_eq!(Some(&1), consumer.peek());
    /// assert_eq!(Some(1), consumer.dequeue());
    /// assert_eq!(None, consumer.peek());
    /// ```
    #[inline]
    pub fn peek(&self) -> Option<&T> {
        self.rb.peek()
    }
}

impl<'a, T> ProducerView<'a, T> {
    /// Adds an `item` to the end of the queue, returns back the `item` if the queue is full
    #[inline]
    pub fn enqueue(&mut self, val: T) -> Result<(), T> {
        unsafe { self.rb.inner_enqueue(val) }
    }

    /// Adds an `item` to the end of the queue, without checking if the queue is full
    ///
    /// # Safety
    ///
    /// See [`Queue::enqueue_unchecked`]
    #[inline]
    pub unsafe fn enqueue_unchecked(&mut self, val: T) {
        self.rb.inner_enqueue_unchecked(val)
    }

    /// Returns if there is any space to enqueue a new item. When this returns true, at
    /// least the first subsequent enqueue will succeed.
    #[inline]
    pub fn ready(&self) -> bool {
        !self.rb.is_full()
    }

    /// Returns the number of elements in the queue
    #[inline]
    pub fn len(&self) -> usize {
        self.rb.len()
    }

    /// Returns true if the queue is empty
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::spsc::Queue;
    ///
    /// let mut queue: Queue<u8, 235> = Queue::new();
    /// let (mut producer, mut consumer) = queue.split();
    /// assert!(producer.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the maximum number of elements the queue can hold
    #[inline]
    pub fn capacity(&self) -> usize {
        self.rb.capacity()
    }
}

#[cfg(test)]
mod tests {
    use std::hash::{Hash, Hasher};

    use super::{Consumer, Producer, Queue};

    use static_assertions::assert_not_impl_any;

    // Ensure a `Queue` containing `!Send` values stays `!Send` itself.
    assert_not_impl_any!(Queue<*const (), 4>: Send);

    // Ensure a `Producer` containing `!Send` values stays `!Send` itself.
    assert_not_impl_any!(Producer<*const (), 4>: Send);

    // Ensure a `Consumer` containing `!Send` values stays `!Send` itself.
    assert_not_impl_any!(Consumer<*const (), 4>: Send);

    #[test]
    fn full() {
        let mut rb: Queue<i32, 3> = Queue::new();

        assert!(!rb.is_full());

        rb.enqueue(1).unwrap();
        assert!(!rb.is_full());

        rb.enqueue(2).unwrap();
        assert!(rb.is_full());
    }

    #[test]
    fn empty() {
        let mut rb: Queue<i32, 3> = Queue::new();

        assert!(rb.is_empty());

        rb.enqueue(1).unwrap();
        assert!(!rb.is_empty());

        rb.enqueue(2).unwrap();
        assert!(!rb.is_empty());
    }

    #[test]
    #[cfg_attr(miri, ignore)] // too slow
    fn len() {
        let mut rb: Queue<i32, 3> = Queue::new();

        assert_eq!(rb.len(), 0);

        rb.enqueue(1).unwrap();
        assert_eq!(rb.len(), 1);

        rb.enqueue(2).unwrap();
        assert_eq!(rb.len(), 2);

        for _ in 0..1_000_000 {
            let v = rb.dequeue().unwrap();
            println!("{}", v);
            rb.enqueue(v).unwrap();
            assert_eq!(rb.len(), 2);
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)] // too slow
    fn try_overflow() {
        const N: usize = 23;
        let mut rb: Queue<i32, N> = Queue::new();

        for i in 0..N as i32 - 1 {
            rb.enqueue(i).unwrap();
        }

        for _ in 0..1_000_000 {
            for i in 0..N as i32 - 1 {
                let d = rb.dequeue().unwrap();
                assert_eq!(d, i);
                rb.enqueue(i).unwrap();
            }
        }
    }

    #[test]
    fn sanity() {
        let mut rb: Queue<i32, 10> = Queue::new();

        let (mut p, mut c) = rb.split();

        assert!(p.ready());

        assert!(!c.ready());

        assert_eq!(c.dequeue(), None);

        p.enqueue(0).unwrap();

        assert_eq!(c.dequeue(), Some(0));
    }

    #[test]
    fn static_new() {
        static mut _Q: Queue<i32, 4> = Queue::new();
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
            let mut v: Queue<Droppable, 4> = Queue::new();
            v.enqueue(Droppable::new()).ok().unwrap();
            v.enqueue(Droppable::new()).ok().unwrap();
            v.dequeue().unwrap();
        }

        assert_eq!(unsafe { COUNT }, 0);

        {
            let mut v: Queue<Droppable, 4> = Queue::new();
            v.enqueue(Droppable::new()).ok().unwrap();
            v.enqueue(Droppable::new()).ok().unwrap();
        }

        assert_eq!(unsafe { COUNT }, 0);
    }

    #[test]
    fn iter() {
        let mut rb: Queue<i32, 4> = Queue::new();

        rb.enqueue(0).unwrap();
        rb.dequeue().unwrap();
        rb.enqueue(1).unwrap();
        rb.enqueue(2).unwrap();
        rb.enqueue(3).unwrap();

        let mut items = rb.iter();

        // assert_eq!(items.next(), Some(&0));
        assert_eq!(items.next(), Some(&1));
        assert_eq!(items.next(), Some(&2));
        assert_eq!(items.next(), Some(&3));
        assert_eq!(items.next(), None);
    }

    #[test]
    fn iter_double_ended() {
        let mut rb: Queue<i32, 4> = Queue::new();

        rb.enqueue(0).unwrap();
        rb.enqueue(1).unwrap();
        rb.enqueue(2).unwrap();

        let mut items = rb.iter();

        assert_eq!(items.next(), Some(&0));
        assert_eq!(items.next_back(), Some(&2));
        assert_eq!(items.next(), Some(&1));
        assert_eq!(items.next(), None);
        assert_eq!(items.next_back(), None);
    }

    #[test]
    fn iter_mut() {
        let mut rb: Queue<i32, 4> = Queue::new();

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
    fn iter_mut_double_ended() {
        let mut rb: Queue<i32, 4> = Queue::new();

        rb.enqueue(0).unwrap();
        rb.enqueue(1).unwrap();
        rb.enqueue(2).unwrap();

        let mut items = rb.iter_mut();

        assert_eq!(items.next(), Some(&mut 0));
        assert_eq!(items.next_back(), Some(&mut 2));
        assert_eq!(items.next(), Some(&mut 1));
        assert_eq!(items.next(), None);
        assert_eq!(items.next_back(), None);
    }

    #[test]
    fn wrap_around() {
        let mut rb: Queue<i32, 4> = Queue::new();

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
        let mut rb: Queue<i32, 3> = Queue::new();
        let (mut p, mut c) = rb.split();
        assert!(!c.ready());
        assert!(p.ready());

        p.enqueue(0).unwrap();

        assert!(c.ready());
        assert!(p.ready());

        p.enqueue(1).unwrap();

        assert!(c.ready());
        assert!(!p.ready());

        c.dequeue().unwrap();

        assert!(c.ready());
        assert!(p.ready());

        c.dequeue().unwrap();

        assert!(!c.ready());
        assert!(p.ready());
    }

    #[test]
    fn clone() {
        let mut rb1: Queue<i32, 4> = Queue::new();
        rb1.enqueue(0).unwrap();
        rb1.enqueue(0).unwrap();
        rb1.dequeue().unwrap();
        rb1.enqueue(0).unwrap();
        let rb2 = rb1.clone();
        assert_eq!(rb1.capacity(), rb2.capacity());
        assert_eq!(rb1.len(), rb2.len());
        assert!(rb1.iter().zip(rb2.iter()).all(|(v1, v2)| v1 == v2));
    }

    #[test]
    fn eq() {
        // generate two queues with same content
        // but different buffer alignment
        let mut rb1: Queue<i32, 4> = Queue::new();
        rb1.enqueue(0).unwrap();
        rb1.enqueue(0).unwrap();
        rb1.dequeue().unwrap();
        rb1.enqueue(0).unwrap();
        let mut rb2: Queue<i32, 4> = Queue::new();
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
            let mut rb1: Queue<i32, 4> = Queue::new();
            rb1.enqueue(0).unwrap();
            rb1.enqueue(0).unwrap();
            rb1.dequeue().unwrap();
            rb1.enqueue(0).unwrap();
            rb1
        };
        let rb2 = {
            let mut rb2: Queue<i32, 4> = Queue::new();
            rb2.enqueue(0).unwrap();
            rb2.enqueue(0).unwrap();
            rb2
        };
        let hash1 = {
            let mut hasher1 = hash32::FnvHasher::default();
            rb1.hash(&mut hasher1);
            hasher1.finish()
        };
        let hash2 = {
            let mut hasher2 = hash32::FnvHasher::default();
            rb2.hash(&mut hasher2);
            hasher2.finish()
        };
        assert_eq!(hash1, hash2);
    }
}

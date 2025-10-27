//! The implementation is based on Dmitry Vyukov's bounded MPMC queue.
//!
//! Source:
//!   - <http://www.1024cores.net/home/lock-free-algorithms/queues/bounded-mpmc-queue>
//!
//! From the [crossbeam-queue](https://github.com/crossbeam-rs/crossbeam/blob/master/crossbeam-queue/src/array_queue.rs) implementation.

use super::{atomic, atomic::Ordering};
use core::cell::UnsafeCell;
use core::fmt;
use core::mem::MaybeUninit;
use core::panic::{RefUnwindSafe, UnwindSafe};

use crate::storage::{OwnedStorage, Storage};

use crossbeam_utils::{Backoff, CachePadded};

use super::{AtomicTargetSize, QueueView, UintSize};

/// A slot in a queue.
struct Slot<T: Sized> {
    /// The current stamp.
    ///
    /// If the stamp equals the tail, this node will be next written to. If it equals head + 1,
    /// this node will be next read from.
    stamp: AtomicTargetSize,

    /// The value in this slot.
    value: UnsafeCell<MaybeUninit<T>>,
}

impl<T> Slot<T> {
    /// Creates a new uninitialized [Slot].
    #[cfg(not(loom))]
    pub const fn new() -> Self {
        Self {
            stamp: AtomicTargetSize::new(0),
            value: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }

    /// Creates a new uninitialized [Slot].
    #[cfg(loom)]
    pub fn new() -> Self {
        Self {
            stamp: AtomicTargetSize::new(0),
            value: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }

    /// Creates a new uninitialized [Slot] with the provided stamp.
    #[cfg(not(loom))]
    pub const fn create_uninit(stamp: UintSize) -> Self {
        Self {
            stamp: AtomicTargetSize::new(stamp),
            value: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }

    /// Creates a new uninitialized [Slot] with the provided stamp.
    #[cfg(loom)]
    pub fn create_uninit(stamp: UintSize) -> Self {
        Self {
            stamp: AtomicTargetSize::new(stamp),
            value: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }
}

impl<T> Default for Slot<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// A bounded multi-producer multi-consumer queue.
///
/// This queue allocates a fixed-capacity buffer on construction, which is used to store pushed
/// elements. The queue cannot hold more elements than the buffer allows. Attempting to push an
/// element into a full queue will fail. Alternatively, [`force_push`] makes it possible for
/// this queue to be used as a ring-buffer. Having a buffer allocated upfront makes this queue
/// a bit faster than [`SegQueue`].
///
/// [`force_push`]: Queue::force_push
/// [`SegQueue`]: super::SegQueue
///
/// # Examples
///
/// ```
/// use heapless::mpmc::Queue;
/// const N: usize = 2;
///
/// let q = Queue::new::<N>();
///
/// assert_eq!(q.enqueue('a'), Ok(()));
/// assert_eq!(q.enqueue('b'), Ok(()));
/// assert_eq!(q.enqueue('c'), Err('c'));
/// assert_eq!(q.dequeue(), Some('a'));
/// ```
pub type Queue<T, const N: usize> = QueueInner<T, OwnedStorage<N>>;

/// Base struct for [`Queue`] and [`QueueView`], generic over the [`Storage`].
///
/// In most cases you should use [`Queue`] or [`QueueView`] directly. Only use this
/// struct if you want to write code that's generic over both.
pub struct QueueInner<T, S: Storage> {
    /// The head of the queue.
    ///
    /// This value is a "stamp" consisting of an index into the buffer and a lap, but packed into a
    /// single `usize`. The lower bits represent the index, while the upper bits represent the lap.
    ///
    /// Elements are popped from the head of the queue.
    head: CachePadded<AtomicTargetSize>,

    /// The tail of the queue.
    ///
    /// This value is a "stamp" consisting of an index into the buffer and a lap, but packed into a
    /// single `usize`. The lower bits represent the index, while the upper bits represent the lap.
    ///
    /// Elements are pushed into the tail of the queue.
    tail: CachePadded<AtomicTargetSize>,

    /// A stamp with the value of `{ lap: 1, index: 0 }`.
    one_lap: UintSize,

    /// The buffer holding slots.
    buffer: UnsafeCell<S::Buffer<Slot<T>>>,
}

impl<T, S: Storage> QueueInner<T, S> {
    /// Attempts to push an element into the queue.
    ///
    /// If the queue is full, the element is returned back as an error.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::mpmc::Queue;
    /// const N: usize = 1;
    ///
    /// let q = Queue::new::<N>();
    ///
    /// assert_eq!(q.enqueue(10), Ok(()));
    /// assert_eq!(q.enqueue(20), Err(20));
    /// ```
    pub fn enqueue(&self, value: T) -> Result<(), T> {
        self.push_or_else(value, |v, tail, _, _| {
            let head = self.head.load(Ordering::Relaxed);

            // If the head lags one lap behind the tail as well...
            if head.wrapping_add(self.one_lap) == tail as UintSize {
                // ...then the queue is full.
                Err(v)
            } else {
                Ok(v)
            }
        })
    }

    /// Returns the number of elements in the queue.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::mpmc::Queue;
    /// const N: usize = 100;
    ///
    /// let q = Queue::new::<N>();
    /// assert_eq!(q.len(), 0);
    ///
    /// q.enqueue(10).unwrap();
    /// assert_eq!(q.len(), 1);
    ///
    /// q.enqueue(20).unwrap();
    /// assert_eq!(q.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        loop {
            // Load the tail, then load the head.
            let tail = self.tail.load(Ordering::SeqCst);
            let head = self.head.load(Ordering::SeqCst);

            // If the tail didn't change, we've got consistent values to work with

            if self.tail.load(Ordering::SeqCst) == tail {
                let hix = head & (self.one_lap - 1);
                let tix = tail & (self.one_lap - 1);

                return if hix < tix {
                    usize::from(tix - hix)
                } else if hix > tix {
                    self.capacity() - usize::from(hix + tix)
                } else if tail == head {
                    0
                } else {
                    self.capacity()
                };
            }
        }
    }

    fn as_ptr(&self) -> *const Slot<T> {
        S::as_ptr(self.buffer.get() as *mut S::Buffer<Slot<T>>) as *const _
    }

    fn push_or_else<F>(&self, mut value: T, f: F) -> Result<(), T>
    where
        F: Fn(T, UintSize, UintSize, &Slot<T>) -> Result<T, T>,
    {
        let backoff = Backoff::new();
        let mut tail = self.tail.load(Ordering::Relaxed);

        loop {
            // Deconstruct the tail.
            let lap_mask = self.one_lap.wrapping_sub(1);
            let index = usize::from(tail & lap_mask);
            let lap = tail & !lap_mask;

            let new_tail = if index + 1 < self.capacity() {
                // Same lap, incremented index.
                // Set to `{ lap: lap, index: index + 1 }`.
                tail + 1
            } else {
                // One lap forward, index wraps around to zero.
                // Set to `{ lap: lap.wrapping_add(1), index: 0 }`.
                lap.wrapping_add(self.one_lap)
            };

            // Inspect the corresponding slot.
            debug_assert!(index < self.capacity());
            // SAFETY: index is a valid offset, and buffer is valid contiguous memory.
            let slot = unsafe { &*self.as_ptr().add(index) };
            let stamp = slot.stamp.load(Ordering::Acquire);

            // If the tail and the stamp match, we may attempt to push.
            if tail == stamp {
                // Try moving the tail.
                match self.tail.compare_exchange_weak(
                    tail,
                    new_tail,
                    Ordering::SeqCst,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => {
                        // Write the value into the slot and update the stamp.
                        unsafe {
                            slot.value.get().write(MaybeUninit::new(value));
                        }
                        slot.stamp.store(tail + 1, Ordering::Release);
                        return Ok(());
                    }
                    Err(t) => {
                        tail = t;
                        backoff.spin();
                    }
                }
            } else if stamp.wrapping_add(self.one_lap) == tail + 1 {
                atomic::fence(Ordering::SeqCst);
                value = f(value, tail, new_tail, slot)?;
                backoff.spin();
                tail = self.tail.load(Ordering::Relaxed);
            } else {
                // Snooze because we need to wait for the stamp to get updated.
                backoff.snooze();
                tail = self.tail.load(Ordering::Relaxed);
            }
        }
    }

    /// Pushes an element into the queue, replacing the oldest element if necessary.
    ///
    /// If the queue is full, the oldest element is replaced and returned,
    /// otherwise `None` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::mpmc::Queue;
    /// const N: usize = 2;
    ///
    /// let q = Queue::new::<N>();
    ///
    /// assert_eq!(q.force_enqueue(10), None);
    /// assert_eq!(q.force_enqueue(20), None);
    /// assert_eq!(q.force_enqueue(30), Some(10));
    /// assert_eq!(q.dequeue(), Some(20));
    /// ```
    pub fn force_enqueue(&self, value: T) -> Option<T> {
        self.push_or_else(value, |v, tail, new_tail, slot| {
            let head = (tail as UintSize).wrapping_sub(self.one_lap);
            let new_head = (new_tail as UintSize).wrapping_sub(self.one_lap);

            // Try moving the head.
            if self
                .head
                .compare_exchange_weak(head, new_head, Ordering::SeqCst, Ordering::Relaxed)
                .is_ok()
            {
                // Move the tail.
                self.tail.store(new_tail, Ordering::SeqCst);

                // Swap the previous value.
                let old = unsafe { slot.value.get().replace(MaybeUninit::new(v)).assume_init() };

                // Update the stamp.
                slot.stamp.store(tail + 1, Ordering::Release);

                Err(old)
            } else {
                Ok(v)
            }
        })
        .err()
    }

    /// Attempts to pop an element from the queue.
    ///
    /// If the queue is empty, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::mpmc::Queue;
    /// const N: usize = 1;
    ///
    /// let q = Queue::new::<N>();
    /// assert_eq!(q.enqueue(10), Ok(()));
    ///
    /// assert_eq!(q.dequeue(), Some(10));
    /// assert!(q.dequeue().is_none());
    /// ```
    pub fn dequeue(&self) -> Option<T> {
        let backoff = Backoff::new();
        let mut head = self.head.load(Ordering::Relaxed);

        loop {
            // Deconstruct the head.
            let lap_mask = self.one_lap.wrapping_sub(1);
            let index = usize::from(head & lap_mask);
            let lap = head & !lap_mask;

            // Inspect the corresponding slot.
            debug_assert!(index < self.capacity());
            // SAFETY: index is a valid offset, and buffer is valid contiguous memory.
            let slot = unsafe { &*self.as_ptr().add(index) };
            let stamp = slot.stamp.load(Ordering::Acquire);

            // If the stamp is ahead of the head by 1, we may attempt to pop.
            if head + 1 == stamp {
                let new = if index + 1 < self.capacity() {
                    // Same lap, incremented index.
                    // Set to `{ lap: lap, index: index + 1 }`.
                    head + 1
                } else {
                    // One lap forward, index wraps around to zero.
                    // Set to `{ lap: lap.wrapping_add(1), index: 0 }`.
                    lap.wrapping_add(self.one_lap)
                };

                // Try moving the head.
                match self.head.compare_exchange_weak(
                    head,
                    new,
                    Ordering::SeqCst,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => {
                        // Read the value from the slot and update the stamp.
                        let msg = unsafe { slot.value.get().read().assume_init() };
                        slot.stamp
                            .store(head.wrapping_add(self.one_lap), Ordering::Release);
                        return Some(msg);
                    }
                    Err(h) => {
                        head = h;
                        backoff.spin();
                    }
                }
            } else if stamp == head {
                atomic::fence(Ordering::SeqCst);
                let tail = self.tail.load(Ordering::Relaxed);

                // If the tail equals the head, that means the channel is empty.
                if tail == head {
                    return None;
                }

                backoff.spin();
                head = self.head.load(Ordering::Relaxed);
            } else {
                // Snooze because we need to wait for the stamp to get updated.
                backoff.snooze();
                head = self.head.load(Ordering::Relaxed);
            }
        }
    }

    /// Returns the maximum number of elements the queue can hold.
    #[inline]
    pub fn capacity(&self) -> usize {
        S::len(self.buffer.get())
    }

    /// Get a reference to the `Queue`, erasing the `N` const-generic.
    ///
    ///
    /// ```rust
    /// # use heapless::mpmc::{Queue, QueueView};
    /// let queue: Queue<u8, 2> = Queue::new();
    /// let view: &QueueView<u8> = queue.as_view();
    /// ```
    ///
    /// It is often preferable to do the same through type coerction, since `Queue<T, N>` implements `Unsize<QueueView<T>>`:
    ///
    /// ```rust
    /// # use heapless::mpmc::{Queue, QueueView};
    /// let queue: Queue<u8, 2> = Queue::new();
    /// let view: &QueueView<u8> = &queue;
    /// ```
    #[inline]
    pub fn as_view(&self) -> &QueueView<T> {
        S::as_mpmc_view(self)
    }

    /// Get a mutable reference to the `Queue`, erasing the `N` const-generic.
    ///
    /// ```rust
    /// # use heapless::mpmc::{Queue, QueueView};
    /// let mut queue: Queue<u8, 2> = Queue::new();
    /// let view: &mut QueueView<u8> = queue.as_mut_view();
    /// ```
    ///
    /// It is often preferable to do the same through type coerction, since `Queue<T, N>` implements `Unsize<QueueView<T>>`:
    ///
    /// ```rust
    /// # use heapless::mpmc::{Queue, QueueView};
    /// let mut queue: Queue<u8, 2> = Queue::new();
    /// let view: &mut QueueView<u8> = &mut queue;
    /// ```
    #[inline]
    pub fn as_mut_view(&mut self) -> &mut QueueView<T> {
        S::as_mpmc_mut_view(self)
    }
}

impl<T, S: Storage> Drop for QueueInner<T, S> {
    fn drop(&mut self) {
        while self.dequeue().is_some() {}
    }
}

unsafe impl<T: Send, const N: usize> Sync for Queue<T, N> {}
unsafe impl<T: Send, const N: usize> Send for Queue<T, N> {}

impl<T, const N: usize> UnwindSafe for Queue<T, N> {}
impl<T, const N: usize> RefUnwindSafe for Queue<T, N> {}

impl<T, const N: usize> Queue<T, N> {
    const _MIN_SIZE: () = assert!(N > 1, "capacity must be at least two");
    const _IS_POW2: () = assert!(N.is_power_of_two(), "capacity must be power of two");
    const _CAP_MAX: () = assert!(N < UintSize::MAX as usize, "capacity maximum exceeded");

    /// Creates a new bounded queue with the given capacity.
    ///
    /// # Panics
    ///
    /// Panics if the capacity is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::mpmc::Queue;
    /// const N: usize = 100;
    ///
    /// let q = Queue::<i32, N>::new();
    /// ```
    #[cfg(not(loom))]
    pub const fn new() -> Self {
        // Head is initialized to `{ lap: 0, index: 0 }`.
        // Tail is initialized to `{ lap: 0, index: 0 }`.
        let head = 0;
        let tail = 0;

        // Allocate a buffer of `cap` slots initialized
        // with stamps.
        let mut slot_count = 0usize;
        let mut buffer: [Slot<T>; N] = [const { Slot::<T>::new() }; N];
        while slot_count < N {
            // Set the stamp to `{ lap: 0, index: i }`.
            buffer[slot_count] = Slot::create_uninit(slot_count as UintSize);
            slot_count += 1;
        }

        // One lap is the smallest power of two greater than `cap`.
        let one_lap = (N + 1).next_power_of_two() as UintSize;

        Self {
            buffer: UnsafeCell::new(buffer),
            one_lap,
            head: CachePadded::new(AtomicTargetSize::new(head)),
            tail: CachePadded::new(AtomicTargetSize::new(tail)),
        }
    }

    /// Creates a new [Queue].
    #[cfg(loom)]
    pub fn new() -> Self {
        // Head is initialized to `{ lap: 0, index: 0 }`.
        // Tail is initialized to `{ lap: 0, index: 0 }`.
        let head = 0;
        let tail = 0;

        // Allocate a buffer of `cap` slots initialized
        // with stamps.
        let mut buffer: [Slot<T>; N] =
            core::array::from_fn(|slot_count| Slot::<T>::create_uninit(slot_count as UintSize));

        // One lap is the smallest power of two greater than `cap`.
        let one_lap = (N + 1).next_power_of_two() as UintSize;

        Self {
            buffer: UnsafeCell::new(buffer),
            one_lap,
            head: CachePadded::new(AtomicTargetSize::new(head)),
            tail: CachePadded::new(AtomicTargetSize::new(tail)),
        }
    }

    /// Returns `true` if the queue is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::mpmc::Queue;
    /// const N: usize = 100;
    ///
    /// let q = Queue::new::<N>();
    ///
    /// assert!(q.is_empty());
    /// q.push(1).unwrap();
    /// assert!(!q.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        let head = self.head.load(Ordering::SeqCst);
        let tail = self.tail.load(Ordering::SeqCst);

        // Is the tail lagging one lap behind head?
        // Is the tail equal to the head?
        //
        // Note: If the head changes just before we load the tail, that means there was a moment
        // when the channel was not empty, so it is safe to just return `false`.
        tail == head
    }

    /// Returns `true` if the queue is full.
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::mpmc::Queue;
    /// const N: usize = 1;
    ///
    /// let q = Queue::new::<N>();
    ///
    /// assert!(!q.is_full());
    /// q.enqueue(1).unwrap();
    /// assert!(q.is_full());
    /// ```
    pub fn is_full(&self) -> bool {
        let tail = self.tail.load(Ordering::SeqCst);
        let head = self.head.load(Ordering::SeqCst);

        // Is the head lagging one lap behind tail?
        //
        // Note: If the tail changes just before we load the head, that means there was a moment
        // when the queue was not full, so it is safe to just return `false`.
        head.wrapping_add(self.one_lap) == tail
    }

    /// Used in `Storage` implementation.
    pub(crate) fn as_view_private(&self) -> &QueueView<T> {
        self
    }
    /// Used in `Storage` implementation.
    pub(crate) fn as_view_mut_private(&mut self) -> &mut QueueView<T> {
        self
    }
}

impl<T, const N: usize> fmt::Debug for Queue<T, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad("Queue { .. }")
    }
}

impl<T, const N: usize> IntoIterator for Queue<T, N> {
    type Item = T;

    type IntoIter = IntoIter<T, N>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter { value: self }
    }
}

/// Represents the iterator container for implementing the [`Iterator`] trait for [Queue].
#[derive(Debug)]
pub struct IntoIter<T, const N: usize> {
    value: Queue<T, N>,
}

impl<T, const N: usize> Iterator for IntoIter<T, N> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let value = &mut self.value;
        let head = value.head.load(Ordering::Relaxed);
        if value.head.load(Ordering::Relaxed) != value.tail.load(Ordering::Relaxed) {
            let index = usize::from(head & (value.one_lap - 1));
            let lap = head & !(value.one_lap - 1);
            // SAFETY: We have mutable access to this, so we can read without
            // worrying about concurrency. Furthermore, we know this is
            // initialized because it is the value pointed at by `value.head`
            // and this is a non-empty queue.
            let val = unsafe {
                debug_assert!(index < N);
                let slot = (&mut *value.buffer.get_mut()).get_unchecked_mut(index);
                slot.value.get().read().assume_init()
            };
            let new = if index + 1 < value.capacity() {
                // Same lap, incremented index.
                // Set to `{ lap: lap, index: index + 1 }`.
                head + 1
            } else {
                // One lap forward, index wraps around to zero.
                // Set to `{ lap: lap.wrapping_add(1), index: 0 }`.
                lap.wrapping_add(value.one_lap)
            };
            value.head.store(new, Ordering::Release);
            Some(val)
        } else {
            None
        }
    }
}

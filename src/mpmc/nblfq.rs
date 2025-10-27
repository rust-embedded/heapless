use core::cell::UnsafeCell;
use core::mem::MaybeUninit;

use crate::storage::{OwnedStorage, Storage};

use super::atomic::{AtomicPtr, Ordering};
use super::{AtomicTargetSize, QueueView, UintSize};

/// Represents the byte-size of the sequence word.
const W: usize = usize::MAX;

/// Represents the inner [Queue] entry slot.
///
/// Provides safe wrappers around the dangerous `unsafe` bits.
#[derive(Debug)]
pub struct Slot<T> {
    sequence: AtomicTargetSize,
    ptr: AtomicPtr<T>,
    elem: UnsafeCell<Option<MaybeUninit<T>>>,
}

impl<T> Slot<T> {
    /// Creates a new [Slot].
    #[cfg(not(loom))]
    pub const fn new() -> Self {
        Self {
            sequence: AtomicTargetSize::new(0),
            ptr: AtomicPtr::new(core::ptr::null_mut()),
            elem: UnsafeCell::new(None),
        }
    }

    /// Creates a new [Slot].
    #[cfg(loom)]
    pub fn new() -> Self {
        Self {
            sequence: AtomicTargetSize::new(0),
            ptr: AtomicPtr::new(core::ptr::null_mut()),
            elem: UnsafeCell::new(None),
        }
    }

    /// Creates a new [Slot].
    #[cfg(not(loom))]
    pub const fn new_sequence(sequence: UintSize) -> Self {
        Self {
            sequence: AtomicTargetSize::new(sequence),
            ptr: AtomicPtr::new(core::ptr::null_mut()),
            elem: UnsafeCell::new(None),
        }
    }

    /// Creates a new [Slot].
    #[cfg(loom)]
    pub fn new_sequence(sequence: UintSize) -> Self {
        Self {
            sequence: AtomicTargetSize::new(sequence),
            ptr: AtomicPtr::new(core::ptr::null_mut()),
            elem: UnsafeCell::new(None),
        }
    }

    /// Creates a new [Slot] from the provided parameters.
    pub fn create(sequence: UintSize, elem: T) -> Self {
        let s = Self {
            sequence: AtomicTargetSize::new(sequence),
            ptr: AtomicPtr::new(core::ptr::null_mut()),
            elem: UnsafeCell::new(Some(MaybeUninit::new(elem))),
        };

        // SAFETY: we just initialized the element, the pointer references valid memory.
        s.ptr.store(unsafe { s.elem_mut_ptr() }, Ordering::Release);

        s
    }

    /// Gets a reference to the sequence.
    pub const fn sequence(&self) -> &AtomicTargetSize {
        &self.sequence
    }

    /// Gets the sequence.
    pub fn load_sequence(&self) -> UintSize {
        self.sequence.load(Ordering::Acquire)
    }

    /// Sets the sequence.
    pub fn store_sequence(&self, seq: UintSize) {
        self.sequence.store(seq, Ordering::Release);
    }

    /// Loads the [Slot] element.
    ///
    /// Returns:
    ///
    /// - `Some(T)`: if the [Slot] has been initialized
    /// - `None`: if the [Slot] is empty.
    pub fn load_element(&self) -> Option<&T> {
        let ptr = self.ptr.load(Ordering::Acquire);
        if ptr.is_null() {
            None
        } else {
            // SAFETY: if non-null, `ptr` references an owned element.
            unsafe { Some(&*ptr) }
        }
    }

    /// Stores the [Slot] sequence and element.
    pub fn store_element(&self, sequence: UintSize, elem: T) {
        self.sequence.store(sequence, Ordering::Release);
        // SAFETY: we run a slight risk of overwriting an entry at the same position.
        // However, we are not in danger of undefined behavior.
        unsafe { (&mut *self.elem.get()).replace(MaybeUninit::new(elem)) };
        // SAFETY: we just iniitialized the element, so the pointer references valid memory.
        self.ptr
            .store(unsafe { self.elem_mut_ptr() }, Ordering::Release);
    }

    /// Gets a mutable pointer to the element.
    ///
    /// # Safety
    ///
    /// Caller must ensure exclusive access to the element.
    #[inline]
    unsafe fn elem_mut_ptr(&self) -> *mut T {
        unsafe { (&mut *self.elem.get()).as_mut().unwrap().as_mut_ptr() }
    }

    /// Clears the [Slot].
    ///
    /// Calls the destructor of the stored element, if it exists.
    pub fn clear(&self) -> Option<T> {
        self.sequence.store(0, Ordering::Release);

        if self.ptr.load(Ordering::Acquire).is_null() {
            None
        } else {
            self.ptr.store(core::ptr::null_mut(), Ordering::Release);
            // SAFETY: we only call `assume_init` on a populated element.
            unsafe { (&mut *self.elem.get()).take().map(|t| t.assume_init()) }
        }
    }

    /// Performs a compare-and-exchange (CAS) operation on the [Slot].
    ///
    /// Returns:
    ///
    /// - `Ok(Slot)`: returns the previous held entry on success
    /// - `Err(Slot)`: returns the replacement entry on error.
    pub fn compare_exchange(&self, cmp: &Self, rep: Self) -> Result<Self, Self> {
        let Ok(s) = self.sequence.compare_exchange(
            cmp.load_sequence(),
            rep.load_sequence(),
            Ordering::AcqRel,
            Ordering::Acquire,
        ) else {
            return Err(rep);
        };

        let Ok(p) = self.ptr.compare_exchange(
            cmp.ptr.load(Ordering::Acquire),
            rep.ptr.load(Ordering::Acquire),
            Ordering::AcqRel,
            Ordering::Acquire,
        ) else {
            self.sequence.store(s, Ordering::Release);
            return Err(rep);
        };

        let t = if p.is_null() {
            None
        } else {
            unsafe { (&mut *self.elem.get()).take() }
        };

        if !rep.ptr.load(Ordering::Acquire).is_null() {
            // SAFETY: we only call `assume_init` on a populated element.
            unsafe {
                if let Some(elem) = rep.elem.into_inner() {
                    (&mut *self.elem.get()).replace(MaybeUninit::new(elem.assume_init()));
                }
            };
        }

        if let Some(elem) = t {
            // SAFETY: we only call `assume_init` on a populated element.
            Ok(Self::create(s, unsafe { elem.assume_init() }))
        } else {
            Ok(Self::new_sequence(s))
        }
    }

    /// Gets whether the [Slot] is empty.
    pub fn is_empty(&self) -> bool {
        self.ptr.load(Ordering::Relaxed).is_null() && unsafe { (&*self.elem.get()).is_none() }
    }

    /// Compares if [Slot] at position `i` is before [Slot] at position `j`.
    pub fn comp(&self, i: UintSize, oth: &Self, j: UintSize) -> bool {
        let l_seq = self.load_sequence();
        let r_seq = oth.load_sequence();

        if l_seq == r_seq {
            i < j
        } else {
            r_seq.wrapping_add(W as UintSize).wrapping_sub(l_seq) < (1 << (UintSize::BITS - 1))
        }
    }

    /// Destructs the [Slot] into its inner element.
    ///
    /// Returns:
    ///
    /// - `Some(T)`: if the [Slot] was initialized.
    /// - `None`: if the [Slot] was uninitialized.
    pub fn into_inner(self) -> Option<T> {
        let ptr = self.ptr.load(Ordering::Acquire);
        if ptr.is_null() {
            None
        } else {
            // SAFETY: if non-null, `ptr` references an owned element.
            unsafe { self.elem.into_inner().map(|e| e.assume_init()) }
        }
    }
}

impl<T> Default for Slot<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: PartialEq> PartialEq for Slot<T> {
    fn eq(&self, oth: &Self) -> bool {
        self.load_sequence() == oth.load_sequence() && self.load_element() == oth.load_element()
    }
}

/// Implement the `Sync` marker trait to share `Slot` across threads.
///
/// # Safety
///
/// All mutability is handled through lock-free guards implemented with atomic operations.
unsafe impl<T> Sync for Slot<T> where T: Sync {}
/// Implement the `Send` marker trait to share `Slot` across threads.
///
/// # Safety
///
/// All mutability is handled through lock-free guards implemented with atomic operations.
unsafe impl<T> Send for Slot<T> where T: Send {}

/// Base struct for [`Queue`] and [`QueueView`], generic over the [`Storage`].
///
/// In most cases you should use [`Queue`] or [`QueueView`] directly. Only use this
/// struct if you want to write code that's generic over both.
pub struct QueueInner<T, S: Storage> {
    head: AtomicTargetSize,
    tail: AtomicTargetSize,
    buffer: UnsafeCell<S::Buffer<Slot<T>>>,
}

impl<T, S: Storage> QueueInner<T, S> {
    fn buffer(&self) -> &[Slot<T>] {
        // SAFETY: buffer is initialized properly, and the pointer references valid memory.
        unsafe { core::slice::from_raw_parts(S::as_ptr(self.buffer.get()), self.capacity()) }
    }

    /// Returns the maximum number of elements the queue can hold.
    #[inline]
    pub fn capacity(&self) -> usize {
        S::len(self.buffer.get())
    }

    /// Gets the [Self] length.
    pub fn len(&self) -> usize {
        let mut len = 0;
        while len < self.capacity() && !self.buffer()[len].is_empty() {
            len = len.saturating_add(1);
        }
        len
    }

    /// Gets whether the [Self] is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
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

    /// Adds an `item` to the end of the queue.
    ///
    /// Returns back the `item` if the queue is full.
    pub fn enqueue(&self, item: T) -> Result<(), T> {
        let mut patience: usize = self.capacity();

        let mut res = Ok(());
        let mut new_slot = Slot::create(0, item);

        'retry: while {
            let c = patience > 0;
            patience = patience.saturating_sub(1);
            c
        } {
            let mut pos = self.load_head();
            let mut prev_pos = self.prev(pos);
            let mut slot;
            let mut prev_slot = &self.buffer()[prev_pos as usize];

            let mut chase_patience = self.capacity();
            'chase: while {
                let c = chase_patience > 0;
                chase_patience = chase_patience.saturating_sub(1);
                c
            } {
                slot = &self.buffer()[pos as usize];
                prev_pos = self.prev(pos);
                prev_slot = &self.buffer()[prev_pos as usize];

                if prev_slot.load_element().is_some() && slot.load_element().is_none() {
                    /* null cell, non-empty predecessor */
                    break 'chase;
                }

                if !prev_slot.comp(prev_pos, slot, pos) {
                    /* found step */
                    if prev_slot.load_element().is_none() && slot.load_element().is_none() {
                        /* empty list */
                        break 'chase;
                    }

                    if prev_slot.load_element().is_some() && slot.load_element().is_some() {
                        /* full list */
                        res = Err(());
                        break 'retry;
                    }
                }

                pos = pos.wrapping_add(1) % self.capacity() as UintSize;
            }

            let mut seq = prev_slot.load_sequence();

            if prev_slot.load_element().is_none() {
                seq = seq.wrapping_add(W as UintSize);
            }

            if pos == 0 {
                seq = seq.wrapping_add(1);
            }

            new_slot.store_sequence(seq);

            match self.buffer()[pos as usize].compare_exchange(&Slot::new_sequence(seq), new_slot) {
                Ok(_) => {
                    self.store_head((pos + 1) % self.capacity() as UintSize);
                    return Ok(());
                }
                Err(v) => new_slot = v,
            }
        }

        // SAFETY: we only call `unwrap` and `assume_init` on populated element.
        res.map_err(|_| new_slot.into_inner().unwrap())
    }

    /// Returns the item in the front of the queue, or `None` if the queue is empty.
    pub fn dequeue(&self) -> Option<T> {
        let mut patience = self.capacity();

        /* retry loop */
        while {
            let c = patience > 0;
            patience = patience.saturating_sub(1);
            c
        } {
            let mut tail = self.load_tail();
            let prev_tail = self.prev(tail);

            let mut prev_slot = &self.buffer()[prev_tail as usize];
            let mut slot = &self.buffer()[tail as usize];

            /* chase the tail */
            while prev_slot.comp(prev_tail, slot, tail) {
                tail = tail.wrapping_add(1) % self.capacity() as UintSize;
                prev_slot = slot;
                slot = &self.buffer()[tail as usize];
            }

            if prev_slot.load_element().is_none() && slot.load_element().is_none() {
                /* empty queue */
                return None;
            }

            let seq = slot.load_sequence().wrapping_add(1);

            if let Ok(slot) =
                self.buffer()[tail as usize].compare_exchange(slot, Slot::new_sequence(seq))
            {
                self.store_tail(tail.wrapping_add(1) % self.capacity() as UintSize);
                return slot.clear();
            }
        }

        None
    }

    /// Helper function to get the previous queue position.
    pub fn prev(&self, i: UintSize) -> UintSize {
        let n = self.capacity() as UintSize;
        (i + n - 1) % n
    }

    /// Gets a reference to the head position.
    pub const fn head(&self) -> &AtomicTargetSize {
        &self.head
    }

    /// Gets the head position.
    pub fn load_head(&self) -> UintSize {
        self.head.load(Ordering::Acquire)
    }

    /// Sets the head position.
    pub fn store_head(&self, head: UintSize) {
        self.head.store(head, Ordering::Release);
    }

    /// Gets a reference to the tail position.
    pub const fn tail(&self) -> &AtomicTargetSize {
        &self.tail
    }

    /// Gets the tail position.
    pub fn load_tail(&self) -> UintSize {
        self.tail.load(Ordering::Acquire)
    }

    /// Sets the tail position.
    pub fn store_tail(&self, tail: UintSize) {
        self.tail.store(tail, Ordering::Release);
    }
}

/// Implement the `Sync` marker trait to share `Slot` across threads.
///
/// # Safety
///
/// All mutability is handled through lock-free guards implemented with atomic operations.
unsafe impl<T, S: Storage> Sync for QueueInner<T, S> where T: Sync {}
/// Implement the `Send` marker trait to share `Slot` across threads.
///
/// # Safety
///
/// All mutability is handled through lock-free guards implemented with atomic operations.
unsafe impl<T, S: Storage> Send for QueueInner<T, S> where T: Send {}

/// A statically allocated multi-producer, multi-consumer queue with a capacity of `N` elements.
///
/// <div class="warning">
///
/// `N` must be a power of 2.
///
/// </div>
///
/// The maximum value of `N` is 128 if the `mpmc_large` feature is not enabled.
pub type Queue<T, const N: usize> = QueueInner<T, OwnedStorage<N>>;

impl<T, const N: usize> Queue<T, N> {
    /// Creates a new [Queue].
    #[cfg(not(loom))]
    pub const fn new() -> Self {
        Self {
            head: AtomicTargetSize::new(0),
            tail: AtomicTargetSize::new(0),
            buffer: UnsafeCell::new([const { Slot::new() }; N]),
        }
    }

    /// Creates a new [Queue].
    #[cfg(loom)]
    pub fn new() -> Self {
        Self {
            head: AtomicTargetSize::new(0),
            tail: AtomicTargetSize::new(0),
            buffer: UnsafeCell::new(core::array::from_fn(|_| Slot::new())),
        }
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

impl<T, const N: usize> Default for Queue<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, S: Storage> Drop for QueueInner<T, S> {
    fn drop(&mut self) {
        // Drop all elements currently in the queue.
        while self.dequeue().is_some() {}
    }
}

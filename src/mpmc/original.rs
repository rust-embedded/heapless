use core::{cell::UnsafeCell, mem::MaybeUninit};

use crate::storage::{OwnedStorage, Storage};

use super::{atomic, AtomicTargetSize, IntSize, QueueView, UintSize};
use atomic::Ordering;

/// Base struct for [`Queue`] and [`QueueView`], generic over the [`Storage`].
///
/// In most cases you should use [`Queue`] or [`QueueView`] directly. Only use this
/// struct if you want to write code that's generic over both.
pub struct QueueInner<T, S: Storage> {
    dequeue_pos: AtomicTargetSize,
    enqueue_pos: AtomicTargetSize,
    buffer: UnsafeCell<S::Buffer<Cell<T>>>,
}

/// A statically allocated multi-producer, multi-consumer queue with a capacity of `N` elements.
///
/// <div class="warning">
///
/// `N` must be a power of 2.
///
/// </div>
///
/// The maximum value of `N` is 128 if the `mpmc_large` feature is not enabled.
///
/// <div class="warning">
///
/// This implementation is not fully lock-free. If a thread or task gets preempted during
/// a `dequeue` or `enqueue` operation, it may prevent other operations from succeeding until
/// it's scheduled again to finish its operation.
///
/// See <https://github.com/rust-embedded/heapless/issues/583> for more details.
///
/// </div>
pub type Queue<T, const N: usize> = QueueInner<T, OwnedStorage<N>>;

impl<T, const N: usize> Queue<T, N> {
    #[cfg(not(loom))]
    /// Creates an empty queue.
    pub const fn new() -> Self {
        const {
            assert!(N > 1);
            assert!(N.is_power_of_two());
            assert!(N < UintSize::MAX as usize);
        }

        let mut cell_count = 0;

        let mut result_cells: [Cell<T>; N] = [const { Cell::new(0) }; N];
        while cell_count != N {
            result_cells[cell_count] = Cell::new(cell_count);
            cell_count += 1;
        }

        Self {
            buffer: UnsafeCell::new(result_cells),
            dequeue_pos: AtomicTargetSize::new(0),
            enqueue_pos: AtomicTargetSize::new(0),
        }
    }

    /// Creates an empty queue.
    #[cfg(loom)]
    pub fn new() -> Self {
        use core::array;

        const {
            assert!(N > 1);
            assert!(N.is_power_of_two());
            assert!(N < UintSize::MAX as usize);
        }

        let result_cells: [Cell<T>; N] = array::from_fn(|idx| Cell::new(idx));

        Self {
            buffer: UnsafeCell::new(result_cells),
            dequeue_pos: AtomicTargetSize::new(0),
            enqueue_pos: AtomicTargetSize::new(0),
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

impl<T, S: Storage> QueueInner<T, S> {
    fn buffer(&self) -> &[Cell<T>] {
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

    fn mask(&self) -> UintSize {
        (S::len(self.buffer.get()) - 1) as _
    }

    /// Returns the item in the front of the queue, or `None` if the queue is empty.
    pub fn dequeue(&self) -> Option<T> {
        unsafe { dequeue(S::as_ptr(self.buffer.get()), &self.dequeue_pos, self.mask()) }
    }

    /// Adds an `item` to the end of the queue.
    ///
    /// Returns back the `item` if the queue is full.
    pub fn enqueue(&self, item: T) -> Result<(), T> {
        unsafe {
            enqueue(
                S::as_ptr(self.buffer.get()),
                &self.enqueue_pos,
                self.mask(),
                item,
            )
        }
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

unsafe impl<T, S: Storage> Sync for QueueInner<T, S> where T: Send {}

struct Cell<T> {
    data: MaybeUninit<T>,
    sequence: AtomicTargetSize,
}

impl<T> Cell<T> {
    #[cfg(not(loom))]
    const fn new(seq: usize) -> Self {
        Self {
            data: MaybeUninit::uninit(),
            sequence: AtomicTargetSize::new(seq as UintSize),
        }
    }
    #[cfg(loom)]
    fn new(seq: usize) -> Self {
        Self {
            data: MaybeUninit::uninit(),
            sequence: AtomicTargetSize::new(seq as UintSize),
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.sequence.load(Ordering::Relaxed) != 0
    }
}

unsafe fn dequeue<T>(
    buffer: *mut Cell<T>,
    dequeue_pos: &AtomicTargetSize,
    mask: UintSize,
) -> Option<T> {
    let mut pos = dequeue_pos.load(Ordering::Relaxed);

    let mut cell;
    loop {
        cell = buffer.add(usize::from(pos & mask));
        let seq = (*cell).sequence.load(Ordering::Acquire);
        let dif = (seq as IntSize).wrapping_sub((pos.wrapping_add(1)) as IntSize);

        match dif.cmp(&0) {
            core::cmp::Ordering::Equal => {
                if dequeue_pos
                    .compare_exchange_weak(
                        pos,
                        pos.wrapping_add(1),
                        Ordering::Relaxed,
                        Ordering::Relaxed,
                    )
                    .is_ok()
                {
                    break;
                }
            }
            core::cmp::Ordering::Less => {
                return None;
            }
            core::cmp::Ordering::Greater => {
                pos = dequeue_pos.load(Ordering::Relaxed);
            }
        }
    }

    let data = (*cell).data.as_ptr().read();
    (*cell)
        .sequence
        .store(pos.wrapping_add(mask).wrapping_add(1), Ordering::Release);
    Some(data)
}

unsafe fn enqueue<T>(
    buffer: *mut Cell<T>,
    enqueue_pos: &AtomicTargetSize,
    mask: UintSize,
    item: T,
) -> Result<(), T> {
    let mut pos = enqueue_pos.load(Ordering::Relaxed);

    let mut cell;
    loop {
        cell = buffer.add(usize::from(pos & mask));
        let seq = (*cell).sequence.load(Ordering::Acquire);
        let dif = (seq as IntSize).wrapping_sub(pos as IntSize);

        match dif.cmp(&0) {
            core::cmp::Ordering::Equal => {
                if enqueue_pos
                    .compare_exchange_weak(
                        pos,
                        pos.wrapping_add(1),
                        Ordering::Relaxed,
                        Ordering::Relaxed,
                    )
                    .is_ok()
                {
                    break;
                }
            }
            core::cmp::Ordering::Less => {
                return Err(item);
            }
            core::cmp::Ordering::Greater => {
                pos = enqueue_pos.load(Ordering::Relaxed);
            }
        }
    }

    (*cell).data.as_mut_ptr().write(item);
    (*cell)
        .sequence
        .store(pos.wrapping_add(1), Ordering::Release);
    Ok(())
}

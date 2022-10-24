use core::{
    future::Future,
    task::{Poll, Waker},
};

use crate::{
    async_impl::ssq::{WakerConsumer, WakerProducer},
    spsc::Producer as HProducer,
};

/// An async producer
pub struct Producer<'queue, T, const N: usize>
where
    T: Unpin,
{
    inner: HProducer<'queue, T, N>,
    producer_waker: WakerProducer<'queue>,
    consumer_waker: WakerConsumer<'queue>,
}

impl<'queue, T, const N: usize> Producer<'queue, T, N>
where
    T: Unpin,
{
    pub(crate) fn new(
        producer: HProducer<'queue, T, N>,
        producer_waker: WakerProducer<'queue>,
        consumer_waker: WakerConsumer<'queue>,
    ) -> Self {
        Self {
            inner: producer,
            producer_waker,
            consumer_waker,
        }
    }

    /// Check if an item can be enqueued.
    ///
    /// If this returns true, at least the first subsequent [`Self::enqueue`] will succeed
    /// immediately.
    pub fn ready(&self) -> bool {
        self.inner.ready()
    }

    /// Returns the maximum number of elements the queue can hold.
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Returns the amount of elements currently in the queue.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Enqueue `value` into the backing queue.
    ///
    /// The returned Future only resolves once the value was
    /// succesfully enqueued.
    pub fn enqueue<'me>(&'me mut self, value: T) -> ProducerFuture<'me, 'queue, T, N> {
        let value = self.inner.enqueue(value).err();
        ProducerFuture {
            producer: self,
            value_to_enqueue: value,
        }
    }

    /// Try to enqueue `value` into the backing queue.
    pub fn try_enqueue(&mut self, value: T) -> Result<(), T> {
        self.inner.enqueue(value)
    }

    /// Try to wake the [`Consumer`](super::Consumer) associated with the backing queue if
    /// it is waiting to be awoken.
    fn wake_consumer(&mut self) {
        self.consumer_waker.dequeue().map(|v| v.wake());
    }

    /// Register `waker` as the waker for this [`Producer`]
    fn register_waker<'v>(&mut self, waker: Waker) -> bool {
        // We can safely overwrite the old waker, as we can only ever have 1 instance
        // of `self` waiting to be awoken.
        self.producer_waker.enqueue(waker).is_none()
    }
}

pub struct ProducerFuture<'producer, 'queue, T, const N: usize>
where
    T: Unpin,
{
    producer: &'producer mut Producer<'queue, T, N>,
    value_to_enqueue: Option<T>,
}

impl<T, const N: usize> Future for ProducerFuture<'_, '_, T, N>
where
    T: Unpin,
{
    type Output = ();

    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> Poll<Self::Output> {
        let try_wake_consumer = |me: &mut Self| {
            me.producer.wake_consumer();
            Poll::Ready(())
        };

        let me = self.get_mut();
        let prod = &mut me.producer;
        let val_to_enqueue = &mut me.value_to_enqueue;

        let value = if let Some(value) = val_to_enqueue.take() {
            value
        } else {
            // Try to wake the consumer because we've enqueued our value
            return try_wake_consumer(me);
        };

        let failed_enqueue_value = if let Some(value) = prod.inner.enqueue(value).err() {
            value
        } else {
            // Try to wake the consumer because we've enqueued our value
            return try_wake_consumer(me);
        };

        me.value_to_enqueue = Some(failed_enqueue_value);

        if !me.producer.register_waker(cx.waker().clone()) {
            // We failed to enqueue the waker for some reason,
            // re-wake immediately.
            cx.waker().wake_by_ref();
        }
        Poll::Pending
    }
}

use core::{
    future::Future,
    task::{Poll, Waker},
};

use crate::{
    async_impl::ssq::{WakerConsumer, WakerProducer},
    spsc::Consumer as HConsumer,
};

/// An async consumer
pub struct Consumer<'queue, T, const N: usize>
where
    T: Unpin,
{
    inner: HConsumer<'queue, T, N>,
    producer_waker: WakerConsumer<'queue>,
    consumer_waker: WakerProducer<'queue>,
}

impl<'queue, T, const N: usize> Consumer<'queue, T, N>
where
    T: Unpin,
{
    pub(crate) fn new(
        consumer: HConsumer<'queue, T, N>,
        producer_waker: WakerConsumer<'queue>,
        consumer_waker: WakerProducer<'queue>,
    ) -> Self {
        Self {
            inner: consumer,
            producer_waker,
            consumer_waker,
        }
    }

    /// Check if there are any items to dequeue.
    ///
    /// When this returns true, at least the first subsequent [`Self::dequeue`] will succeed immediately
    pub fn ready(&self) -> bool {
        self.inner.ready()
    }

    /// Returns the maximum number of elements the queue can hold
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Returns the amount of elements currently in the queue
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Dequeue an item from the backing queue.
    ///
    /// The returned future only resolves once an item was succesfully
    /// dequeued.
    pub fn dequeue<'me>(&'me mut self) -> ConsumerFuture<'me, 'queue, T, N> {
        ConsumerFuture {
            consumer: self,
            dequeued_value: None,
        }
    }

    /// Attempt to dequeue an item from the backing queue.
    pub fn try_dequeue(&mut self) -> Option<T> {
        self.try_wake_producer();

        self.inner.dequeue()
    }

    /// Try to wake the [`Producer`](super::Producer) associated with the backing queue if
    /// it is waiting to be awoken.
    fn try_wake_producer(&mut self) {
        self.producer_waker.dequeue().map(|w| w.wake());
    }

    /// Register `waker` as the waker for this [`Consumer`]
    fn register_waker<'v>(&mut self, waker: Waker) {
        // We can safely overwrite the old waker, as we can only ever have 1 instance
        // of `self` waiting to be awoken.
        self.consumer_waker.enqueue(waker);
    }
}

pub struct ConsumerFuture<'consumer, 'queue, T, const N: usize>
where
    T: Unpin,
{
    consumer: &'consumer mut Consumer<'queue, T, N>,
    dequeued_value: Option<T>,
}

impl<T, const N: usize> Future for ConsumerFuture<'_, '_, T, N>
where
    T: Unpin,
{
    type Output = T;

    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> Poll<Self::Output> {
        let try_wake_producer = |me: &mut Self, value| {
            me.consumer.try_wake_producer();
            return Poll::Ready(value);
        };

        let me = self.get_mut();
        let con = &mut me.consumer;

        if let Some(value) = me.dequeued_value.take() {
            // Try to wake the producer because we managed to
            // dequeue a value
            return try_wake_producer(me, value);
        }

        me.dequeued_value = con.inner.dequeue();
        if let Some(value) = me.dequeued_value.take() {
            // Try to wake the producer because we managed to
            // dequeue a value
            try_wake_producer(me, value)
        } else {
            me.consumer.register_waker(cx.waker().clone());

            Poll::Pending
        }
    }
}

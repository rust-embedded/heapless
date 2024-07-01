//! Collections of `Send`-able things are `Send`

use heapless::{
    histbuf::HistoryBufferView,
    spsc::{Consumer, ConsumerView, Producer, ProducerView, Queue, QueueView},
    HistoryBuffer, Vec, VecView,
};

#[test]
fn send() {
    struct IsSend;

    unsafe impl Send for IsSend {}

    fn is_send<T>()
    where
        T: Send + ?Sized,
    {
    }

    is_send::<Consumer<IsSend, 4>>();
    is_send::<ConsumerView<IsSend>>();
    is_send::<Producer<IsSend, 4>>();
    is_send::<ProducerView<IsSend>>();
    is_send::<Queue<IsSend, 4>>();
    is_send::<QueueView<IsSend>>();
    is_send::<Vec<IsSend, 4>>();
    is_send::<VecView<IsSend>>();
    is_send::<HistoryBuffer<IsSend, 4>>();
    is_send::<HistoryBufferView<IsSend>>();
}

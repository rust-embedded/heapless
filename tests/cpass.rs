//! Collections of `Send`-able things are `Send`

use heapless::{
    spsc::{Consumer, MultiCore, Producer, Queue},
    HistoryBuffer, Vec,
};

#[test]
fn send() {
    struct IsSend;

    unsafe impl Send for IsSend {}

    fn is_send<T>()
    where
        T: Send,
    {
    }

    is_send::<Consumer<IsSend, usize, MultiCore, 4>>();
    is_send::<Producer<IsSend, usize, MultiCore, 4>>();
    is_send::<Queue<IsSend, usize, MultiCore, 4>>();
    is_send::<Vec<IsSend, 4>>();
    is_send::<HistoryBuffer<IsSend, 4>>();
}

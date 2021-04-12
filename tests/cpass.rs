//! Collections of `Send`-able things are `Send`

use heapless::{
    spsc::{Consumer, Producer, Queue},
    HistoryBuffer, VecBase,
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

    is_send::<Consumer<IsSend, usize, 4>>();
    is_send::<Producer<IsSend, usize, 4>>();
    is_send::<Queue<IsSend, usize, 4>>();
    is_send::<VecBase<IsSend, usize, 4>>();
    is_send::<VecBase<IsSend, u8, 4>>();
    is_send::<VecBase<IsSend, u16, 4>>();
    is_send::<HistoryBuffer<IsSend, 4>>();
}

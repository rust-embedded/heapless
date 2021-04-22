//! Collections of non-`Send`-able things are *not* `Send`

use core::marker::PhantomData;

use heapless::{
    spsc::{Consumer, Producer, Queue},
    HistoryBuffer, Vec,
};

type NotSend = PhantomData<*const ()>;

fn is_send<T>()
where
    T: Send,
{
}

fn main() {
    is_send::<Consumer<NotSend, 4>>();
    is_send::<Producer<NotSend, 4>>();
    is_send::<Queue<NotSend, 4>>();
    is_send::<Vec<NotSend, 4>>();
    is_send::<HistoryBuffer<NotSend, 4>>();
}

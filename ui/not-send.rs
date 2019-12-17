//! Collections of non-`Send`-able things are *not* `Send`

use core::marker::PhantomData;

use heapless::{
    consts,
    spsc::{Consumer, Producer, Queue},
};

type NotSend = PhantomData<*const ()>;

fn is_send<T>()
where
    T: Send,
{
}

fn main() {
    is_send::<Consumer<NotSend, consts::U4>>();
    is_send::<Producer<NotSend, consts::U4>>();
    is_send::<Queue<NotSend, consts::U4>>();
    is_send::<Vec<NotSend, consts::U4>>();
}

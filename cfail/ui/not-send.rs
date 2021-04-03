//! Collections of non-`Send`-able things are *not* `Send`

use core::marker::PhantomData;

use heapless::{
    spsc::{Consumer, Producer, Queue},
};

type NotSend = PhantomData<*const ()>;

fn is_send<T>()
where
    T: Send,
{
}

fn main() {
    is_send::<Consumer<NotSend, _, 4>>();
    is_send::<Producer<NotSend, _, 4>>();
    is_send::<Queue<NotSend, _, 4>>();
    is_send::<heapless::Vec<NotSend, 4>>();
}

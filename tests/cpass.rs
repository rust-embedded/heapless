use std::marker::PhantomData;

use generic_array::typenum::op;
use heapless::{
    consts::*,
    spsc::{Consumer, Producer, Queue},
    HistoryBuffer, Vec,
};

#[test]
fn send() {
    // Collections of `Send`-able things are `Send`
    struct IsSend;

    unsafe impl Send for IsSend {}

    fn is_send<T>()
    where
        T: Send,
    {
    }

    is_send::<Consumer<IsSend, U4>>();
    is_send::<Producer<IsSend, U4>>();
    is_send::<Queue<IsSend, U4>>();
    is_send::<Vec<IsSend, U4, u8>>();
    is_send::<HistoryBuffer<IsSend, U4>>();
}

#[test]
fn vec() {
    // Vecs that are sized within the bounds of their length types
    let _s: PhantomData<Vec<u8, U200, u8>>;
    let _s: PhantomData<Vec<u8, U255, u8>>;
    let _s: PhantomData<Vec<u8, U256, u16>>;
    let _s: PhantomData<Vec<u8, op!(U65536 - U1), u16>>;
    let _s: PhantomData<Vec<u8, U65536, usize>>;
    let _s: PhantomData<Vec<u8, U100000, usize>>;
}

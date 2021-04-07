//! Vec with u16 length and capacity of 65536

use core::marker::PhantomData;

use heapless::{consts::*, Vec};

fn main() {
    let _s: PhantomData<Vec<u8, U65536, u16>>;
}

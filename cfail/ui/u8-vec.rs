//! Vec with u8 length and capacity of 256

use core::marker::PhantomData;

use heapless::{consts::*, Vec};

fn main() {
    let _s: PhantomData<Vec<u8, U256, u8>>;
}

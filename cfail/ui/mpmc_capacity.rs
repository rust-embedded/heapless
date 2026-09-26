use core::mem::ManuallyDrop;
use heapless::mpmc::Queue;

const _: () = {
    #[allow(deprecated)]
    // 256 > u8::MAX
    let _ = ManuallyDrop::new(Queue::<u8, 256, u8>::new());
};

fn main() {}

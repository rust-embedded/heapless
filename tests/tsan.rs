extern crate heapless;

use std::thread;

use heapless::RingBuffer;

#[test]
fn tsan() {
    static mut RB: RingBuffer<i32, [i32; 4]> = RingBuffer::new();

    unsafe { RB.split() }.0.enqueue(0).unwrap();

    thread::spawn(|| {
        unsafe { RB.split() }.0.enqueue(1).unwrap();
    });

    thread::spawn(|| {
        unsafe { RB.split() }.1.dequeue().unwrap();
    });
}

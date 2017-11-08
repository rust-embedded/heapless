extern crate heapless;

use std::thread;

use heapless::RingBuffer;

#[test]
fn once() {
    static mut RB: RingBuffer<i32, [i32; 4]> = RingBuffer::new();

    unsafe { RB.split() }.0.enqueue(0).unwrap();

    thread::spawn(|| {
        unsafe { RB.split() }.0.enqueue(1).unwrap();
    });

    thread::spawn(|| {
        unsafe { RB.split() }.1.dequeue().unwrap();
    });
}

#[test]
fn twice() {
    static mut RB: RingBuffer<i32, [i32; 8]> = RingBuffer::new();

    unsafe { RB.split() }.0.enqueue(0).unwrap();
    unsafe { RB.split() }.0.enqueue(1).unwrap();

    thread::spawn(|| {
        unsafe { RB.split() }.0.enqueue(2).unwrap();
        unsafe { RB.split() }.0.enqueue(3).unwrap();
    });

    thread::spawn(|| {
        unsafe { RB.split() }.1.dequeue().unwrap();
        unsafe { RB.split() }.1.dequeue().unwrap();
    });
}

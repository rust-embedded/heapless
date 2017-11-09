#![deny(warnings)]

extern crate heapless;
extern crate scoped_threadpool;

use std::thread;

use heapless::RingBuffer;
use scoped_threadpool::Pool;

#[test]
fn once() {
    static mut RB: RingBuffer<i32, [i32; 4]> = RingBuffer::new();

    let rb = unsafe { &mut RB };

    rb.enqueue(0).unwrap();

    let (mut p, mut c) = rb.split();

    p.enqueue(1).unwrap();

    thread::spawn(move || {
        p.enqueue(1).unwrap();
    });

    thread::spawn(move || {
        c.dequeue().unwrap();
    });
}

#[test]
fn twice() {
    static mut RB: RingBuffer<i32, [i32; 8]> = RingBuffer::new();

    let rb = unsafe { &mut RB };

    rb.enqueue(0).unwrap();
    rb.enqueue(1).unwrap();

    let (mut p, mut c) = rb.split();

    thread::spawn(move || {
        p.enqueue(2).unwrap();
        p.enqueue(3).unwrap();
    });

    thread::spawn(move || {
        c.dequeue().unwrap();
        c.dequeue().unwrap();
    });
}

#[test]
fn scoped() {
    let mut rb: RingBuffer<i32, [i32; 4]> = RingBuffer::new();

    rb.enqueue(0).unwrap();

    {
        let (mut p, mut c) = rb.split();

        Pool::new(2).scoped(move |scope| {
            scope.execute(move || {
                p.enqueue(1).unwrap();
            });

            scope.execute(move || {
                c.dequeue().unwrap();
            });
        });
    }

    rb.dequeue().unwrap();
}

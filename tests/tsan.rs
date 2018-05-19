#![deny(warnings)]

extern crate generic_array;
extern crate heapless;
extern crate scoped_threadpool;

use std::thread;

use generic_array::typenum::Unsigned;
use heapless::consts::*;
use heapless::RingBuffer;
use scoped_threadpool::Pool;

#[cfg(feature = "const-fn")]
#[test]
fn once() {
    static mut RB: RingBuffer<i32, U4> = RingBuffer::new();

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

#[cfg(feature = "const-fn")]
#[test]
fn twice() {
    static mut RB: RingBuffer<i32, U8> = RingBuffer::new();

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
    let mut rb: RingBuffer<i32, U4> = RingBuffer::new();

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

#[test]
fn contention() {
    type N = U1024;

    let mut rb: RingBuffer<u8, N> = RingBuffer::new();

    {
        let (mut p, mut c) = rb.split();

        Pool::new(2).scoped(move |scope| {
            scope.execute(move || {
                let mut sum: u32 = 0;

                for i in 0..(2 * N::to_u32()) {
                    sum = sum.wrapping_add(i);
                    while let Err(_) = p.enqueue(i as u8) {}
                }

                println!("producer: {}", sum);
            });

            scope.execute(move || {
                let mut sum: u32 = 0;

                for _ in 0..(2 * N::to_u32()) {
                    loop {
                        match c.dequeue() {
                            Some(v) => {
                                sum = sum.wrapping_add(v as u32);
                                break;
                            }
                            _ => {}
                        }
                    }
                }

                println!("consumer: {}", sum);
            });
        });
    }

    assert!(rb.is_empty());
}

#[test]
fn unchecked() {
    type N = U1024;

    let mut rb: RingBuffer<u8, N> = RingBuffer::new();

    for _ in 0..N::to_usize() / 2 {
        rb.enqueue(1).unwrap();
    }

    {
        let (mut p, mut c) = rb.split();

        Pool::new(2).scoped(move |scope| {
            scope.execute(move || {
                for _ in 0..N::to_usize() / 2 {
                    p.enqueue_unchecked(2);
                }
            });

            scope.execute(move || {
                let mut sum: usize = 0;

                for _ in 0..N::to_usize() / 2 {
                    sum = sum.wrapping_add(usize::from(unsafe { c.dequeue_unchecked() }));
                }

                assert_eq!(sum, N::to_usize() / 2);
            });
        });
    }

    assert_eq!(rb.len(), N::to_usize() / 2);
}

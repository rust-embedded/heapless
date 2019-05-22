#![deny(rust_2018_compatibility)]
#![deny(rust_2018_idioms)]
#![deny(warnings)]

use std::{sync::mpsc, thread};

use generic_array::typenum::Unsigned;
use heapless::{consts::*, mpmc::Q64, spsc};
use scoped_threadpool::Pool;

#[test]
fn once() {
    static mut RB: spsc::Queue<i32, U4> = spsc::Queue(heapless::i::Queue::new());

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
    static mut RB: spsc::Queue<i32, U4> = spsc::Queue(heapless::i::Queue::new());

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
    let mut rb: spsc::Queue<i32, U4> = spsc::Queue::new();

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

    let mut rb: spsc::Queue<u8, N> = spsc::Queue::new();

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
fn mpmc_contention() {
    const N: u32 = 64;

    static Q: Q64<u32> = Q64::new();

    let (s, r) = mpsc::channel();
    Pool::new(2).scoped(|scope| {
        let s1 = s.clone();
        scope.execute(move || {
            let mut sum: u32 = 0;

            for i in 0..(16 * N) {
                sum = sum.wrapping_add(i);
                while let Err(_) = Q.enqueue(i) {}
            }

            s1.send(sum).unwrap();
        });

        let s2 = s.clone();
        scope.execute(move || {
            let mut sum: u32 = 0;

            for _ in 0..(16 * N) {
                loop {
                    match Q.dequeue() {
                        Some(v) => {
                            sum = sum.wrapping_add(v);
                            break;
                        }
                        _ => {}
                    }
                }
            }

            s2.send(sum).unwrap();
        });
    });

    assert_eq!(r.recv().unwrap(), r.recv().unwrap());
}

#[test]
fn unchecked() {
    type N = U1024;

    let mut rb: spsc::Queue<u8, N> = spsc::Queue::new();

    for _ in 0..N::to_usize() / 2 {
        rb.enqueue(1).unwrap();
    }

    {
        let (mut p, mut c) = rb.split();

        Pool::new(2).scoped(move |scope| {
            scope.execute(move || {
                for _ in 0..N::to_usize() / 2 {
                    unsafe {
                        p.enqueue_unchecked(2);
                    }
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

#[test]
fn len_properly_wraps() {
    type N = U3;
    let mut rb: spsc::Queue<u8, N> = spsc::Queue::new();

    rb.enqueue(1).unwrap();
    assert_eq!(rb.len(), 1);
    rb.dequeue();
    assert_eq!(rb.len(), 0);
    rb.enqueue(2).unwrap();
    assert_eq!(rb.len(), 1);
    rb.enqueue(3).unwrap();
    assert_eq!(rb.len(), 2);
    rb.enqueue(4).unwrap();
    assert_eq!(rb.len(), 3);
}

#[test]
fn iterator_properly_wraps() {
    type N = U3;
    let mut rb: spsc::Queue<u8, N> = spsc::Queue::new();

    rb.enqueue(1).unwrap();
    rb.dequeue();
    rb.enqueue(2).unwrap();
    rb.enqueue(3).unwrap();
    rb.enqueue(4).unwrap();
    let expected = [2, 3, 4];
    let mut actual = [0, 0, 0];
    for (idx, el) in rb.iter().enumerate() {
        actual[idx] = *el;
    }
    assert_eq!(expected, actual)
}

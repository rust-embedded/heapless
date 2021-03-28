use heapless::{spsc::Queue};

fn main() {
    let mut q: Queue<u8, _, _, 4> = Queue::new();

    let (_p, mut _c) = q.split();
    q.enqueue(0).unwrap();
    _c.dequeue();
}

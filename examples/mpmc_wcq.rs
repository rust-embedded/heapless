use wcq::Queue;

fn main() {
    let q = Queue::<_, 2>::new();
    for _ in 0..255 {
        assert!(q.enqueue(0).is_ok());
        assert_eq!(q.dequeue(), Some(0));
    }

    // Queue is empty, this should not block forever.
    assert_eq!(q.dequeue(), None);
}

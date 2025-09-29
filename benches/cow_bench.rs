use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;

use heapless::{
    cow::CowStr,
    string::{String, StringView},
};

fn bench_cowstr(c: &mut Criterion) {
    // Owned string
    let mut owned_buf: String<32> = String::new();
    owned_buf.push_str("owned hello").unwrap();
    let owned_s: String<32> = owned_buf;

    // Borrowed string (temporary buffer)
    let mut temp_buf: String<32> = String::new();
    temp_buf.push_str("hello").unwrap();

    // Static string
    let mut static_buf: String<32> = String::new();
    static_buf.push_str("static hello").unwrap();
    let static_sv: &'static StringView<usize> = Box::leak(Box::new(static_buf)).as_view();

    // Borrowed benchmark
    c.bench_function("CowStr::Borrowed to_owned", |b| {
        b.iter(|| {
            let sv = temp_buf.as_view();
            let cow: CowStr<32> = CowStr::Borrowed(sv);
            black_box(cow.to_owned());
        });
    });

    // Static benchmark
    c.bench_function("CowStr::Static to_owned", |b| {
        b.iter(|| {
            let cow: CowStr<32> = CowStr::Static(static_sv);
            black_box(cow.to_owned());
        });
    });

    // Owned benchmark
    c.bench_function("CowStr::Owned clone", |b| {
        b.iter(|| {
            let cow: CowStr<32> = CowStr::Owned(owned_s.clone());
            black_box(cow.to_owned());
        });
    });
}

criterion_group!(benches, bench_cowstr);
criterion_main!(benches);

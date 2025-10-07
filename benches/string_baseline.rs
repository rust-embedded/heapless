//! Baseline benchmarks for heapless String operations.
//!
//! This benchmark suite measures the performance characteristics of basic
//! String operations to establish a baseline for comparison.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use heapless::{cow::CowStr, String};

fn create_test_string<const N: usize>(content: &str) -> String<N> {
    String::try_from(content).expect("String too long for capacity")
}

/// Baseline function that always copies into a new String<N>.
fn baseline_always_copy<const N: usize>(input: &String<N>) -> CowStr<'_, N> {
    CowStr::Owned(input.clone())
}

/// Function that sometimes mutates the string (requires clone).
fn baseline_conditional_mutation<const N: usize>(
    input: &String<N>,
    needs_mutation: bool,
) -> CowStr<'_, N> {
    if needs_mutation {
        let mut owned = input.clone();
        let _ = owned.push_str("_mutated");
        CowStr::Owned(owned)
    } else {
        CowStr::Borrowed(input.as_view())
    }
}

fn bench_string_baseline(c: &mut Criterion) {
    let mut group = c.benchmark_group("string_baseline");

    let test_str: String<128> = create_test_string("test string for comparison");

    group.bench_function("always_copy", |b| {
        b.iter(|| {
            let result = baseline_always_copy(black_box(&test_str));
            black_box(result)
        });
    });

    group.bench_function("no_mutation", |b| {
        b.iter(|| {
            let result = baseline_conditional_mutation(black_box(&test_str), false);
            black_box(result)
        });
    });

    group.bench_function("with_mutation", |b| {
        b.iter(|| {
            let result = baseline_conditional_mutation(black_box(&test_str), true);
            black_box(result)
        });
    });

    group.finish();
}

fn bench_string_creation(c: &mut Criterion) {
    let mut group = c.benchmark_group("string_creation");

    let short_str: String<16> = create_test_string("hello");
    let medium_str: String<64> = create_test_string("This is a medium length test string");
    let long_str: String<256> = create_test_string("This is a much longer test string that contains more characters to properly test the performance characteristics");

    group.bench_function("clone_short", |b| {
        b.iter(|| black_box(short_str.clone()));
    });

    group.bench_function("clone_medium", |b| {
        b.iter(|| black_box(medium_str.clone()));
    });

    group.bench_function("clone_long", |b| {
        b.iter(|| black_box(long_str.clone()));
    });

    group.finish();
}

fn bench_string_as_str(c: &mut Criterion) {
    let mut group = c.benchmark_group("string_as_str");

    let test_str: String<64> = create_test_string("test string for as_str");

    group.bench_function("as_str", |b| {
        b.iter(|| black_box(&test_str).as_str());
    });

    group.finish();
}

fn bench_string_clone_for_size<const N: usize>(
    group: &mut criterion::BenchmarkGroup<criterion::measurement::WallTime>,
    content: &str,
    size: usize,
) {
    let test_str: String<N> = create_test_string(content);

    group.bench_with_input(BenchmarkId::new("clone", size), &size, |b, _| {
        b.iter(|| black_box(&test_str).clone());
    });
}

fn bench_string_clone_sizes(c: &mut Criterion) {
    let mut group = c.benchmark_group("string_clone_sizes");

    bench_string_clone_for_size::<16>(&mut group, "short", 16);
    bench_string_clone_for_size::<64>(
        &mut group,
        "This is a medium length string for testing",
        64,
    );
    bench_string_clone_for_size::<256>(
        &mut group,
        "This is a very long string that we use to test the performance with different string sizes and capacities to ensure proper benchmarking",
        256,
    );

    group.finish();
}

fn bench_string_vs_clone(c: &mut Criterion) {
    let mut group = c.benchmark_group("string_vs_clone");

    let test_str: String<128> =
        create_test_string("This is a string that would normally be cloned in every operation");

    group.bench_function("clone_read_only", |b| {
        b.iter(|| {
            let s = black_box(&test_str).clone();
            let _result = black_box(s.as_str());
        });
    });

    group.bench_function("clone_when_needed", |b| {
        b.iter(|| {
            let s = black_box(&test_str).clone();
            let _owned = black_box(s);
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_string_baseline,
    bench_string_creation,
    bench_string_as_str,
    bench_string_clone_sizes,
    bench_string_vs_clone
);
criterion_main!(benches);

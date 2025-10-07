//! Criterion benchmarks for `CowStr` enum.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use heapless::{cow::CowStr, String};

fn create_test_string<const N: usize>(content: &str) -> String<N> {
    String::try_from(content).expect("String too long for capacity")
}

fn cowstr_clone_on_mutation<'a, const N: usize>(
    input: &'a String<N>,
    needs_mutation: bool,
) -> CowStr<'a, N> {
    if needs_mutation {
        let mut owned = input.clone();
        let _ = owned.push_str("_mutated");
        CowStr::Owned(owned)
    } else {
        CowStr::Borrowed(input.as_view())
    }
}

fn bench_baseline_vs_cowstr(c: &mut Criterion) {
    let mut group = c.benchmark_group("baseline_vs_cowstr");

    let test_str: String<128> = create_test_string("test string for comparison");

    group.bench_function("cowstr_no_mutation", |b| {
        b.iter(|| {
            let result = cowstr_clone_on_mutation(black_box(&test_str), false);
            black_box(result)
        });
    });

    group.bench_function("cowstr_with_mutation", |b| {
        b.iter(|| {
            let result = cowstr_clone_on_mutation(black_box(&test_str), true);
            black_box(result)
        });
    });

    group.finish();
}

fn bench_cowstr_creation(c: &mut Criterion) {
    let mut group = c.benchmark_group("cowstr_creation");

    let short_str: String<16> = create_test_string("hello");
    let medium_str: String<64> = create_test_string("This is a medium length test string");
    let long_str: String<256> = create_test_string("This is a much longer test string that contains more characters to properly test the performance characteristics of the CowStr type with different sizes");

    group.bench_function("borrowed_short", |b| {
        b.iter(|| {
            let view = black_box(&short_str).as_view();
            black_box(CowStr::<16>::Borrowed(view))
        });
    });

    group.bench_function("borrowed_medium", |b| {
        b.iter(|| {
            let view = black_box(&medium_str).as_view();
            black_box(CowStr::<64>::Borrowed(view))
        });
    });

    group.bench_function("borrowed_long", |b| {
        b.iter(|| {
            let view = black_box(&long_str).as_view();
            black_box(CowStr::<256>::Borrowed(view))
        });
    });

    group.bench_function("owned_short", |b| {
        b.iter(|| {
            let s = black_box(short_str.clone());
            black_box(CowStr::<16>::Owned(s))
        });
    });

    group.bench_function("owned_medium", |b| {
        b.iter(|| {
            let s = black_box(medium_str.clone());
            black_box(CowStr::<64>::Owned(s))
        });
    });

    group.bench_function("owned_long", |b| {
        b.iter(|| {
            let s = black_box(long_str.clone());
            black_box(CowStr::<256>::Owned(s))
        });
    });

    group.finish();
}

fn bench_cowstr_as_str(c: &mut Criterion) {
    let mut group = c.benchmark_group("cowstr_as_str");

    let test_str: String<64> = create_test_string("test string for as_str");
    let borrowed = CowStr::<64>::Borrowed(test_str.as_view());
    let owned = CowStr::<64>::Owned(test_str.clone());
    let static_string: &'static String<64> = Box::leak(Box::new(test_str.clone()));
    let static_cow = CowStr::<64>::Static(static_string.as_view());

    group.bench_function("borrowed", |b| {
        b.iter(|| black_box(&borrowed).as_str());
    });

    group.bench_function("static", |b| {
        b.iter(|| black_box(&static_cow).as_str());
    });

    group.bench_function("owned", |b| {
        b.iter(|| black_box(&owned).as_str());
    });

    group.finish();
}

fn bench_cowstr_to_owned_for_size<const N: usize>(
    group: &mut criterion::BenchmarkGroup<criterion::measurement::WallTime>,
    content: &str,
    size: usize,
) {
    let test_str: String<N> = create_test_string(content);
    let borrowed = CowStr::<N>::Borrowed(test_str.as_view());
    let owned = CowStr::<N>::Owned(test_str.clone());

    group.bench_with_input(BenchmarkId::new("borrowed", size), &size, |b, _| {
        b.iter(|| black_box(&borrowed).to_owned());
    });

    group.bench_with_input(BenchmarkId::new("owned", size), &size, |b, _| {
        b.iter(|| black_box(&owned).to_owned());
    });
}

fn bench_cowstr_to_owned(c: &mut Criterion) {
    let mut group = c.benchmark_group("cowstr_to_owned");

    bench_cowstr_to_owned_for_size::<16>(&mut group, "short", 16);
    bench_cowstr_to_owned_for_size::<64>(
        &mut group,
        "This is a medium length string for testing",
        64,
    );
    bench_cowstr_to_owned_for_size::<256>(
        &mut group,
        "This is a very long string that we use to test the performance of the to_owned method on CowStr with different string sizes and capacities to ensure proper benchmarking",
        256,
    );

    group.finish();
}

fn bench_cowstr_type_checks(c: &mut Criterion) {
    let mut group = c.benchmark_group("cowstr_type_checks");

    let test_str: String<64> = create_test_string("test");
    let borrowed = CowStr::<64>::Borrowed(test_str.as_view());
    let owned = CowStr::<64>::Owned(test_str.clone());
    let static_string: &'static String<64> = Box::leak(Box::new(test_str.clone()));
    let static_cow = CowStr::<64>::Static(static_string.as_view());

    group.bench_function("is_borrowed", |b| {
        b.iter(|| black_box(&borrowed).is_borrowed());
    });

    group.bench_function("is_static", |b| {
        b.iter(|| black_box(&static_cow).is_static());
    });

    group.bench_function("is_owned", |b| {
        b.iter(|| black_box(&owned).is_owned());
    });

    group.finish();
}

fn bench_cowstr_vs_clone(c: &mut Criterion) {
    let mut group = c.benchmark_group("cowstr_vs_clone");

    let test_str: String<128> =
        create_test_string("This is a string that would normally be cloned in every operation");

    group.bench_function("cowstr_borrowed_read_only", |b| {
        b.iter(|| {
            let cow = CowStr::<128>::Borrowed(black_box(&test_str).as_view());
            let _result = black_box(cow.as_str());
        });
    });

    group.bench_function("string_clone_read_only", |b| {
        b.iter(|| {
            let s = black_box(&test_str).clone();
            let _result = black_box(s.as_str());
        });
    });

    group.bench_function("cowstr_to_owned_when_needed", |b| {
        b.iter(|| {
            let cow = CowStr::<128>::Borrowed(black_box(&test_str).as_view());
            let _owned = black_box(cow.to_owned());
        });
    });

    group.bench_function("string_clone_when_needed", |b| {
        b.iter(|| {
            let s = black_box(&test_str).clone();
            let _owned = black_box(s);
        });
    });

    group.finish();
}

fn bench_cowstr_from(c: &mut Criterion) {
    let mut group = c.benchmark_group("cowstr_from");

    let test_str: String<64> = create_test_string("test string");

    group.bench_function("from_stringview", |b| {
        b.iter(|| {
            let view = black_box(&test_str).as_view();
            black_box(CowStr::<64>::from(view))
        });
    });

    group.bench_function("from_string", |b| {
        b.iter(|| {
            let s = black_box(&test_str).clone();
            black_box(CowStr::<64>::from(s))
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_baseline_vs_cowstr,
    bench_cowstr_creation,
    bench_cowstr_as_str,
    bench_cowstr_to_owned,
    bench_cowstr_type_checks,
    bench_cowstr_vs_clone,
    bench_cowstr_from
);
criterion_main!(benches);

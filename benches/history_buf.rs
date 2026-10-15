//! Benchmarks for `HistoryBuf`, modelled on the sliding-window search from
//! <https://github.com/rust-embedded/heapless/issues/598>.

use std::hint::black_box;

use divan::{counter::BytesCount, Bencher};
use heapless::HistoryBuf;

/// Window sizes to benchmark, both powers of two and not.
const WINDOW_SIZES: &[usize] = &[8, 9, 16, 31, 32, 64, 100, 128, 1000, 1024];
const TOTAL_BYTES: usize = 8 * 1024 * 1024;

/// A needle of `N` non-zero bytes.
fn needle<const N: usize>() -> [u8; N] {
    core::array::from_fn(|i| (i % 255) as u8 + 1)
}

/// Zero-filled input ending with the needle, so that a search only succeeds on the last byte.
fn input<const N: usize>() -> Vec<u8> {
    let mut data = vec![0; TOTAL_BYTES - N];
    data.extend_from_slice(&needle::<N>());
    data
}

/// Writes every input byte into a window.
///
/// The final window state is kept observable, otherwise the optimizer removes the whole loop.
#[divan::bench(consts = WINDOW_SIZES)]
fn write<const N: usize>(bencher: Bencher) {
    bencher
        .counter(BytesCount::new(TOTAL_BYTES))
        .with_inputs(input::<N>)
        .bench_refs(|data| {
            let mut window: HistoryBuf<u8, N> = HistoryBuf::new();
            for &byte in data.iter() {
                window.write(byte);
            }
            black_box(&window);
        });
}

/// Writes every input byte into a window and compares the window against the needle after each
/// write, returning the position at which the needle was found.
#[divan::bench(consts = WINDOW_SIZES)]
fn write_and_search<const N: usize>(bencher: Bencher) {
    let needle = needle::<N>();
    bencher
        .counter(BytesCount::new(TOTAL_BYTES))
        .with_inputs(input::<N>)
        .bench_refs(|data| {
            let mut window: HistoryBuf<u8, N> = HistoryBuf::new();
            for (index, &byte) in data.iter().enumerate() {
                window.write(byte);
                if window.oldest_ordered().eq(&needle) {
                    return Some(index);
                }
            }
            None
        });
}

fn main() {
    divan::main();
}

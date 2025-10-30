#![no_main]

use libfuzzer_sys::fuzz_target;

use heapless::{String, Vec};

fn test_string<const N: usize>(data: &[u8]) {
    let v16_be = data
        .chunks_exact(2)
        .map(|c| u16::from_be_bytes([c[0], c[1]]))
        .collect::<Vec<u16, N>>();

    let v16_le = data
        .chunks_exact(2)
        .map(|c| u16::from_le_bytes([c[0], c[1]]))
        .collect::<Vec<u16, N>>();

    String::<N>::from_utf16(v16_be.as_slice()).ok();
    String::<N>::from_utf16(v16_le.as_slice()).ok();

    Vec::<u8, N>::from_slice(data)
        .map_err(|_| ())
        .and_then(|v| String::<N>::from_utf8(v).map_err(|_| ()))
        .ok();
}

fuzz_target!(|data: &[u8]| {
    match data.len() {
        0 => (),
        len if len <= 16 => test_string::<16>(data),
        len if len <= 32 => test_string::<32>(data),
        len if len <= 64 => test_string::<64>(data),
        len if len <= 128 => test_string::<128>(data),
        len if len <= 256 => test_string::<256>(data),
        len if len <= 512 => test_string::<512>(data),
        len if len <= 1024 => test_string::<1024>(data),
        len if len <= 2048 => test_string::<2048>(data),
        len if len <= 4096 => test_string::<4096>(data),
        _ => (),
    }
});

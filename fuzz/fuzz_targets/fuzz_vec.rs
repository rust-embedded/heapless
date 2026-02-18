#![no_main]

use libfuzzer_sys::fuzz_target;

use heapless::Vec;

fn test_vec<const N: usize>(data: &[u8]) {
    if let Ok(vec) = Vec::<u8, N>::from_slice(data) {
        assert_eq!(vec.as_slice(), data);
    }
}

fuzz_target!(|data: &[u8]| {
    match data.len() {
        0 => (),
        len if len <= 16 => test_vec::<16>(data),
        len if len <= 32 => test_vec::<32>(data),
        len if len <= 64 => test_vec::<64>(data),
        len if len <= 128 => test_vec::<128>(data),
        len if len <= 256 => test_vec::<256>(data),
        len if len <= 512 => test_vec::<512>(data),
        len if len <= 1024 => test_vec::<1024>(data),
        len if len <= 2048 => test_vec::<2048>(data),
        len if len <= 4096 => test_vec::<4096>(data),
        _ => (),
    }
});

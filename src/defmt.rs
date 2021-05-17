//! Defmt implementations for heapless types
//!

use crate::Vec;
use defmt::Formatter;

impl<T, const N: usize> defmt::Format for Vec<T, N>
    where
        T: defmt::Format,
{
    fn format(&self, fmt: Formatter<'_>) {
        defmt::write!(fmt, "{=[?]}", self.as_slice())
    }
}

impl<const N: usize> defmt::Format for crate::String<N>
    where
        u8: defmt::Format,
{
    fn format(&self, fmt: Formatter<'_>) {
        defmt::write!(fmt, "{=str}", self.as_str());
    }
}

#[cfg(test)]
mod tests {
    use crate::Vec;
    use defmt::Format;

    #[test]
    /// Tests encoding Vec with defmt, asserting these types may be serialized
    /// Note: the exact wire format is NOT checked since its an unstable implementation detail of an external crate.
    /// based on https://github.com/knurling-rs/defmt/blob/697a8e807bd766a80ada2d57514a9da1232dbc9a/tests/encode.rs#L523
    fn test_defmt_format_vec() {
        let val: Vec<_, 8> = Vec::from_slice(b"abc").unwrap();

        let mut f = defmt::InternalFormatter::new();
        let g = defmt::Formatter { inner: &mut f };
        val.format(g);
        f.finalize();
    }

    /// Tests encoding String with defmt, asserting these types may be serialized
    /// Note: the exact wire format is NOT checked since its an unstable implementation detail of an external crate.
    /// based loosely on https://github.com/knurling-rs/defmt/blob/main/tests/encode.rs#L483
    #[test]
    fn test_defmt_format_str() {
        let mut val: crate::String<32> = crate::String::new();
        val.push_str("foo").unwrap();

        let mut f = defmt::InternalFormatter::new();
        let g = defmt::Formatter { inner: &mut f };
        val.format(g);
        f.finalize();
    }
}

//! Defmt implementations for heapless types

use crate::{storage::Storage, vec::VecInner};
use defmt::Formatter;

impl<T, S: Storage> defmt::Format for VecInner<T, S>
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

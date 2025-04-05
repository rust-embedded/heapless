//! Defmt implementations for heapless types

use crate::{
    string::{StringInner, StringStorage},
    vec::{VecInner, VecStorage},
};
use defmt::Formatter;

impl<T, S: VecStorage<T> + ?Sized> defmt::Format for VecInner<T, S>
where
    T: defmt::Format,
{
    fn format(&self, fmt: Formatter<'_>) {
        defmt::write!(fmt, "{=[?]}", self.as_slice())
    }
}

impl<S: StringStorage + ?Sized> defmt::Format for StringInner<S>
where
    u8: defmt::Format,
{
    fn format(&self, fmt: Formatter<'_>) {
        defmt::write!(fmt, "{=str}", self.as_str());
    }
}

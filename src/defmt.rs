//! Defmt implementations for heapless types

use crate::{
    len_type::LenType,
    string::{StringInner, StringStorage},
    vec::{VecInner, VecStorage},
};
use defmt::Formatter;

impl<T, LenT: LenType, S: VecStorage<T> + ?Sized> defmt::Format for VecInner<T, LenT, S>
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

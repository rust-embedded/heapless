use core::fmt;
#[cfg(feature = "std")]
use std::error::Error;

const CAPERROR: &'static str = "insufficient capacity";

/// Capacity error returned when container's capacity is not enough to complete the operation
#[derive(Debug, PartialEq)]
pub struct CapacityError {
    /// Maximum characters allowed
    pub maximum: usize,
    /// Encountered number of characters
    pub encountered: usize,
}

#[cfg(feature = "std")]
impl Error for CapacityError {
    fn description(&self) -> &str {
        CAPERROR
    }
}

impl fmt::Display for CapacityError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}: maximum {}, encountered {}",
            CAPERROR, self.maximum, self.encountered
        )
    }
}

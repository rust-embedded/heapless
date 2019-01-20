use core::fmt;

const CAPERROR: &str = "insufficient capacity";

/// Capacity error returned when container's capacity is not enough to complete the operation
#[derive(Debug, PartialEq)]
pub struct CapacityError {
    /// Maximum characters allowed
    pub maximum: usize,
    /// Encountered number of characters
    pub encountered: usize,
}

#[cfg(feature = "std")]
impl std::error::Error for CapacityError {}

impl fmt::Display for CapacityError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}: maximum {}, encountered {}",
            CAPERROR, self.maximum, self.encountered
        )
    }
}

/// Capacity error returned when container's capacity is not enough to complete the operation
#[derive(Fail, Debug, PartialEq, Eq)]
#[fail(display= "Insufficient capacity: maximum {}, encountered {}", maximum, encountered)]
pub struct CapacityError
{
    /// Maximum characters allowed
    pub maximum: usize,
    /// Encountered number of characters
    pub encountered: usize,
}

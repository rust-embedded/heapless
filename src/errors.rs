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

/// Result returned from insertion operation
/// Generic over the rest of the data, that cound not be inserted
#[derive(Debug)]
pub struct CapacityResult<T> (Result<(), (T, CapacityError)>);

impl<T> CapacityResult<T>  {

    /// Construct an Ok variant of this result
    fn ok() -> Self {
        CapacityResult(Ok(()))
    }

    /// Construct an Err variant of this result
    /// containing the rest and the capacity error
    fn err(rest: T, err: CapacityError) -> Self {
        CapacityResult(Err((rest, err)))
    }

    /// Use the result as an proper core::Result with references
    pub fn as_result(&self) -> Result<(), &CapacityError> {
        self.0.as_ref()
            .map(|_| ())
            .map_err(|e| &e.1)
    }

    /// Use the result as a proper core::Result with mutable references
    pub fn as_mut_result(&mut self) -> Result<(), &mut CapacityError> {
        self.0.as_mut()
            .map(|_| ())
            .map_err(|e| &mut e.1)
    }

    /// Convert the result into a proper core::Result
    ///
    /// This can be used to perform error handling,
    /// when the returned `rest` is not relevant
    pub fn into_result(self) -> Result<(), CapacityError> {
        self.0.map_err(|e| e.1)
    }

    /// Use the result as an optional reference to `rest`,
    /// which could not be inserted due to capacity errors
    pub fn as_rest(&self) -> Option<&T> {
        self.0.as_ref()
            .err()
            .map(|e| &e.0)
    }

    /// Use the result as an optional mutable reference to `rest`,
    /// which could not be inserted due to capacity errors
    pub fn as_mut_rest(&mut self) -> Option<&mut T> {
        self.0.as_mut()
            .err()
            .map(|e| &mut e.0)
    }

    /// Convert the result to an optional `rest`,
    /// which could not be inserted due to capacity errors
    pub fn into_rest(self) -> Option<T> {
        self.0.err()
            .map(|e| e.0)
    }

    /// Use the result as an optional reference to an error
    pub fn as_err(&self) -> Option<&CapacityError> {
        self.0.as_ref()
            .err()
            .map(|e| &e.1)
    }

    /// Use the result as an optional mutable reference to an error
    pub fn as_mut_err(&mut self) -> Option<&mut CapacityError> {
        self.0.as_mut()
            .err()
            .map(|e| &mut e.1)
    }

    /// Convert the result to an optional error
    pub fn as_err(&self) -> Option<CapacityError> {
        self.0.err()
            .map(|e| e.1)
    }

    /// returns `true` if the result is ok
    pub fn is_ok(&self) -> bool {
        self.0.is_ok()
    }

    /// returns `true` if the result is err
    pub fn is_err(&self) -> bool {
        self.0.is_err()
    }

}


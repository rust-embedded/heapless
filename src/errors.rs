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

impl CapacityError {
    /// Create an capacity error where the maximum capacity is exeeded be one
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::CapacityError;
    /// let x = CapacityError::one_more_than(42);
    /// assert_eq!(x, CapacityError {
    ///     maximum: 42,
    ///     encountered: 43,
    /// });
    pub fn one_more_than(maximum: usize) -> Self {
        CapacityError {
            maximum,
            encountered: maximum + 1,
        }
    }
}

/// Result returned from insertion operation
/// Generic over the rest of the data, that cound not be inserted
#[derive(Debug)]
pub struct CapacityResult<T> (Result<(), (T, CapacityError)>);

impl<T> CapacityResult<T>  {

    /// Construct an Ok variant of this result
    pub fn ok() -> Self {
        CapacityResult(Ok(()))
    }

    /// Construct an Err variant of this result
    /// containing the rest and the capacity error
    pub fn err(rest: T, err: CapacityError) -> Self {
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
    /// This method can be used to perform error handling,
    /// when the returned `rest` is not relevant.
    /// The returned result can by used with the `?` operator
    ///
    /// # Examples
    ///
    /// basic usage
    ///
    /// ```
    /// use heapless::CapacityResult;
    /// use heapless::CapacityError;
    ///
    /// let a: CapacityResult<i32> = CapacityResult::ok();
    /// assert_eq!(a.into_result(), Ok(()));
    ///
    /// let b = CapacityResult::err(42, CapacityError::one_more_than(1));
    /// assert_eq!(b.into_result(), Err(CapacityError::one_more_than(1)));
    /// ```
    ///
    /// For error handling
    ///
    /// ```
    /// use heapless::CapacityResult;
    /// use heapless::CapacityError;
    ///
    /// fn do_it() -> Result<(), CapacityError> {
    ///     let x = CapacityResult::err(42, CapacityError::one_more_than(1));
    ///     x.into_result()?;
    ///     Ok(())
    /// }
    ///
    /// do_it();
    ///
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
    ///
    /// This method can be used to try to recover from the given CapacityError
    /// by performing some operation with the element that could not be inserted
    ///
    /// # Examples
    ///
    /// Basic usage
    ///
    /// ```
    /// use heapless::CapacityResult;
    /// use heapless::CapacityError;
    ///
    /// let x = CapacityResult::err(42, CapacityError::one_more_than(1));
    /// assert_eq!(x.into_rest(), Some(42));
    /// ```
    ///
    /// Recovering from an error:
    ///
    /// ```
    /// use heapless::CapacityResult;
    /// use heapless::CapacityError;
    ///
    /// fn recover(i: i32) -> bool {
    ///     // ...
    ///     true
    /// }
    ///
    /// let x = CapacityResult::err(42, CapacityError::one_more_than(1));
    /// if let Some(r) = x.into_rest() {
    ///     if !recover(r) {
    ///         panic!("Failed while recovering");
    ///     }
    /// }
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::CapacityResult;
    /// use heapless::CapacityError;
    ///
    /// let x = CapacityResult::err(42, CapacityError::one_more_than(1));
    /// assert_eq!(x.into_err(), Some(CapacityError::one_more_than(1)));
    pub fn into_err(self) -> Option<CapacityError> {
        self.0.err()
            .map(|e| e.1)
    }

    /// returns `true` if the result is ok
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::CapacityResult;
    /// let x: CapacityResult<i32> = CapacityResult::ok();
    /// assert!(x.is_ok());
    /// ```
    pub fn is_ok(&self) -> bool {
        self.0.is_ok()
    }

    /// returns `true` if the result is err
    ///
    /// # Examples
    ///
    /// ```
    /// use heapless::CapacityResult;
    /// use heapless::CapacityError;
    /// let x: CapacityResult<i32> = CapacityResult::err(42, CapacityError::one_more_than(1));
    /// assert!(x.is_err());
    /// ```
    pub fn is_err(&self) -> bool {
        self.0.is_err()
    }

}


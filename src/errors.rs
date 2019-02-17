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

/// Result returned from insertion operation.
/// The insertion operation can either succeed
/// or fail due to an capacity overflow.
///
/// If the operation suceeded, the result is ok,
/// containing an value of thype `T`.
/// For many insert operation this value is `()`,
/// however if the insertion replaced an existing value in an collection,
/// the return value might be `Some(replaced_value)`.
///
/// If the operation failed fue to an capacity overflow,
/// this result contains two pieces of data
///   - an `CapacityError`, which describes by how for the capacity was exceeded
///   - an `rest` of type `R`, which is the rest of the data, that could not be inserted.
#[derive(Debug)]
#[must_use = "this `CapacityResult` might be an error variant and must be used"]
pub struct CapacityResult<T, R> (Result<T, (R, CapacityError)>);

impl<T, R> CapacityResult<T, R> {

    /// Construct an Ok variant of this result
    pub fn ok(value: T) -> Self {
        CapacityResult(Ok(value))
    }

    /// Construct an Err variant of this result
    /// containing the rest and the capacity error
    pub fn err(rest: R, err: CapacityError) -> Self {
        CapacityResult(Err((rest, err)))
    }

    /// Use the result as an proper core::Result with references
    pub fn as_result(&self) -> Result<&T , &CapacityError> {
        self.0.as_ref()
            .map_err(|e| &e.1)
    }

    /// Use the result as a proper core::Result with mutable references
    pub fn as_mut_result(&mut self) -> Result<&mut T, &mut CapacityError> {
        self.0.as_mut()
            .map_err(|e| &mut e.1)
    }

    /// Convert the result into a proper core::Result
    ///
    /// This method can be used to perform error handling,
    /// when the returned `rest` is not relevant.
    /// The returned result can by used with the `?` operator.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::CapacityResult;
    /// use heapless::CapacityError;
    ///
    /// let a: CapacityResult<(), i32> = CapacityResult::ok(());
    /// assert_eq!(a.into_result(), Ok(()));
    ///
    /// let b: CapacityResult<(), i32> = CapacityResult::err(42, CapacityError::one_more_than(1));
    /// assert_eq!(b.into_result(), Err(CapacityError::one_more_than(1)));
    /// ```
    ///
    /// For error handling:
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
    pub fn into_result(self) -> Result<T, CapacityError> {
        self.0.map_err(|e| e.1)
    }

    /// Use the result as an optional reference to `rest`,
    /// which could not be inserted due to capacity errors.
    pub fn as_rest(&self) -> Option<&R> {
        self.0.as_ref()
            .err()
            .map(|e| &e.0)
    }

    /// Use the result as an optional mutable reference to `rest`,
    /// which could not be inserted due to capacity errors.
    pub fn as_mut_rest(&mut self) -> Option<&mut R> {
        self.0.as_mut()
            .err()
            .map(|e| &mut e.0)
    }

    /// Convert the result to an optional `rest`,
    /// which could not be inserted due to capacity errors.
    ///
    /// This method can be used to try to recover from the given CapacityError
    /// by performing some operation with the element that could not be inserted.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::CapacityResult;
    /// use heapless::CapacityError;
    ///
    /// let x: CapacityResult<(), i32> = CapacityResult::err(42, CapacityError::one_more_than(1));
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
    /// let x: CapacityResult<(), i32> = CapacityResult::err(42, CapacityError::one_more_than(1));
    /// if let Some(r) = x.into_rest() {
    ///     if !recover(r) {
    ///         panic!("Failed while recovering");
    ///     }
    /// }
    /// ```
    pub fn into_rest(self) -> Option<R> {
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

    /// Convert the result to an optional error.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::CapacityResult;
    /// use heapless::CapacityError;
    ///
    /// let x: CapacityResult<(), i32> = CapacityResult::err(42, CapacityError::one_more_than(1));
    /// assert_eq!(x.into_err(), Some(CapacityError::one_more_than(1)));
    pub fn into_err(self) -> Option<CapacityError> {
        self.0.err()
            .map(|e| e.1)
    }

    /// Returns `true` if the result is ok.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::CapacityResult;
    ///
    /// let x: CapacityResult<(), i32> = CapacityResult::ok(());
    /// assert!(x.is_ok());
    /// ```
    pub fn is_ok(&self) -> bool {
        self.0.is_ok()
    }

    /// Returns `true` if the result is an error.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::CapacityResult;
    /// use heapless::CapacityError;
    ///
    /// let x: CapacityResult<(), i32> = CapacityResult::err(42, CapacityError::one_more_than(1));
    /// assert!(x.is_err());
    /// ```
    pub fn is_err(&self) -> bool {
        self.0.is_err()
    }

    /// Unwrap the result to access the contained value.
    ///
    /// # Panics
    ///
    /// Panics if the result was an error.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::CapacityResult;
    ///
    /// let x: CapacityResult<(), i32> = CapacityResult::ok(());
    /// x.unwrap(); // does not panic
    /// ```
    ///
    /// Panic on error:
    ///
    /// ```should_panic
    /// use heapless::CapacityResult;
    /// use heapless::CapacityError;
    ///
    /// let x: CapacityResult<(), i32> = CapacityResult::err(42, CapacityError::one_more_than(1));
    /// x.unwrap(); // panics
    /// ```
    pub fn unwrap(self) -> T {
        self.into_result().unwrap()
    }

    /// Unwrap the result to access the contained value
    /// and panic with the given message if it was an error.
    ///
    /// # Panics
    ///
    /// Panics if the result was an error
    pub fn expect(self, msg: &str) -> T {
        self.into_result().expect(msg)
    }

    /// Ignore this result, but consume it.
    ///
    /// This serves the same purpose as calling `Result::ok()`
    /// but not using the `ok` value.
    pub fn ignore(self) {
        self.0.ok();
    }

    /// If the result is an error, transform the contained rest.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::CapacityResult;
    /// use heapless::CapacityError;
    ///
    /// let x: CapacityResult<(), i32> = CapacityResult::err(42, CapacityError::one_more_than(1));
    /// assert_eq!(x.map_rest(|i| i+1).into_rest(), Some(43));
    /// ```
    pub fn map_rest<S, F: FnOnce(R) -> S>(self, f: F) -> CapacityResult<T, S> {
        CapacityResult(self.0.map_err(|(rest, err)| (f(rest), err)))
    }

    /// If the result is ok, transform the value
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::CapacityResult;
    /// use heapless::CapacityError;
    ///
    /// let x: CapacityResult<i32, i32> = CapacityResult::ok(42);
    /// assert_eq!(x.map(|i| i+1).into_result().ok(), Some(43));
    /// ```
    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> CapacityResult<U, R> {
        CapacityResult(self.0.map(f))
    }

    /// Transform the error variant, ignore the contained rest.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use heapless::CapacityResult;
    /// use heapless::CapacityError;
    ///
    /// #[derive(Debug, PartialEq, Eq)]
    /// struct FooError;
    ///
    /// let x: CapacityResult<(), i32> = CapacityResult::err(42, CapacityError::one_more_than(1));
    /// assert_eq!(x.map_err(|_| FooError).err(), Some(FooError));
    /// ```
    pub fn map_err<E, F: FnOnce(CapacityError) -> E>(self, f: F) -> Result<T, E> {
        self.0.map_err(|(_, err)| f(err))
    }

}



use crate::location::Location;

#[derive(Debug, Clone)]
pub struct FrontEndError<T> {
    pub kind: T,
    pub location: Location,
    pub error: String,
}

impl<T> FrontEndError<T> {
    pub fn new(kind: T, location: Location, error: String) -> Self {
        Self {
            kind,
            location,
            error,
        }
    }

    pub fn with_context(self, context: &str) -> Self {
        Self {
            error: format!("{}; {}", context, self.error),
            ..self
        }
    }
}

/// Error that is returned when the last layer of the compiler fails.
/// This error is closest to the user and should be the most descriptive.
/// It should be created at the last possible moment (e.g. at a point
/// where one can still get the module (<=> file) of the error).
#[derive(Debug, Clone)]
pub struct LastLayerError {
    pub error: String,
    pub location: Location,
    pub module: String,
}

impl LastLayerError {
    pub fn from_fe<T>(error: FrontEndError<T>, module: String) -> Self {
        Self {
            error: error.error,
            location: error.location,
            module,
        }
    }

    pub fn with_context(self, context: &str) -> Self {
        Self {
            error: format!("{}; {}", context, self.error),
            ..self
        }
    }
}

use super::fmt::{Debug, Display};

/// See [`std::error::Error`]
pub trait Error: Display + Debug {}

// hax does not support default trait methods, hence this blanket-implemented trait.
trait ErrorDefaults {
    /// See [`std::error::Error::description`]
    fn description(&self) -> &str;
}

// Excluded, not opaque, for Lean: aeneas cannot translate the `&'static str` body,
// and an opaque method leaves the instance referring to an undefined function.
#[cfg_attr(hax_backend_lean, hax_lib::exclude)]
impl<T: Error> ErrorDefaults for T {
    fn description(&self) -> &str {
        "description() is deprecated; use Display"
    }
}

#[cfg(test)]
mod tests {
    use super::{Error, ErrorDefaults};
    use crate::fmt::{Display, Formatter, Result};

    struct ModelError;

    impl Display for ModelError {
        fn fmt(&self, f: &mut Formatter) -> Result {
            Result::Ok(())
        }
    }

    #[cfg(not(hax_backend_fstar))]
    impl crate::fmt::Debug for ModelError {
        fn fmt(&self, f: &mut Formatter) -> Result {
            Result::Ok(())
        }
    }

    impl Error for ModelError {}

    #[derive(Debug)]
    struct StdError;

    impl core::fmt::Display for StdError {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            f.write_str("std error")
        }
    }

    impl core::error::Error for StdError {}

    // Runs the `Display`/`Debug` impls, which `description` never calls.
    #[test]
    fn test_display_impls_run() {
        let mut f = Formatter;
        let _: Result = Display::fmt(&ModelError, &mut f);
        #[cfg(not(hax_backend_fstar))]
        let _: Result = crate::fmt::Debug::fmt(&ModelError, &mut f);
        assert_eq!(std::format!("{}", StdError), "std error");
    }

    #[test]
    fn test_description_matches_core() {
        #[allow(deprecated)]
        let expected = core::error::Error::description(&StdError);
        assert_eq!(ErrorDefaults::description(&ModelError), expected);
    }
}

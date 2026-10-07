use super::fmt::{Debug, Display};

const DEPRECATED_DESCRIPTION: &str = "description() is deprecated; use Display";

/// See [`std::error::Error`]
pub trait Error: Display + Debug {
    /// See [`std::error::Error::description`]
    // F* has no default methods: there, `ErrorDefaults` provides it. Opaque for
    // Lean, where Aeneas cannot translate a `&str` return; a hand-written Lean
    // definition provides it instead.
    #[cfg(not(hax_backend_fstar))]
    #[cfg_attr(hax_backend_lean, hax_lib::opaque)]
    fn description(&self) -> &str {
        DEPRECATED_DESCRIPTION
    }
}

// `Error::description` for F*, where a trait cannot provide it: this blanket
// impl gives it to every `Error`, including clients' own.
#[cfg(any(hax_backend_fstar, test))]
pub(crate) trait ErrorDefaults {
    fn description(&self) -> &str;
}

#[cfg(any(hax_backend_fstar, test))]
impl<T: Error> ErrorDefaults for T {
    fn description(&self) -> &str {
        DEPRECATED_DESCRIPTION
    }
}

#[cfg(test)]
mod tests {
    use super::{Error, ErrorDefaults};
    use crate::fmt::{Debug, Display, Formatter, Result};

    struct ModelError;

    // Required by `Error`; `description` never formats the value.
    #[cfg_attr(coverage_nightly, coverage(off))]
    impl Display for ModelError {
        fn fmt(&self, _: &mut Formatter) -> Result {
            Result::Ok(())
        }
    }

    // Required by `Error`; `description` never formats the value. F*'s `Debug`
    // has a blanket impl.
    #[cfg(not(hax_backend_fstar))]
    #[cfg_attr(coverage_nightly, coverage(off))]
    impl Debug for ModelError {
        fn fmt(&self, _: &mut Formatter) -> Result {
            Result::Ok(())
        }
    }

    impl Error for ModelError {}

    #[derive(Debug)]
    struct StdError;

    // Required by `core::error::Error`; `description` never formats the value.
    #[cfg_attr(coverage_nightly, coverage(off))]
    impl core::fmt::Display for StdError {
        fn fmt(&self, _: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            Ok(())
        }
    }

    impl core::error::Error for StdError {}

    #[test]
    fn test_description_matches_core() {
        #[allow(deprecated)]
        let expected = core::error::Error::description(&StdError);
        #[cfg(not(hax_backend_fstar))]
        assert_eq!(Error::description(&ModelError), expected);
        assert_eq!(ErrorDefaults::description(&ModelError), expected);
    }
}

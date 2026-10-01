//! Equivalence tests for `core::error::*`.
//! Rust-only: the model's `description` lives in `ErrorDefaults`, not `Error`.

#[cfg(test)]
mod description {
    use core::error::Error;
    use core::fmt;

    #[derive(Debug)]
    struct E;

    impl fmt::Display for E {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("e")
        }
    }

    impl Error for E {}

    #[test]
    fn test_description_default() {
        #[allow(deprecated)]
        let description = E.description();
        assert_eq!(description, "description() is deprecated; use Display");
    }
}

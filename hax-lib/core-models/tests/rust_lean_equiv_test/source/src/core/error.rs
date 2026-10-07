//! Equivalence tests for `core::error::*`.

// TODO(client-fmt-impls): Aeneas cannot translate the `Display`/`Debug` impls
// that implementing `Error` requires, so these tests run in Rust only.
#[cfg(test)]
mod description {
    use core::error::Error;
    use core::fmt;

    struct E;

    impl fmt::Display for E {
        fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result {
            Ok(())
        }
    }

    impl fmt::Debug for E {
        fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result {
            Ok(())
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

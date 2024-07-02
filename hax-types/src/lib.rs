//! This crate contains the type definitions that are used to communicate between:
//!  - the command line (the `cargo-hax` binary);
//!  - the custom rustc driver;
//!  - the hax engine (the `hax-engine` binary).
//!  
//! Those three component send and receive messages in JSON or CBOR on
//! stdin and stdout.

pub(crate) mod prelude;

/// The CLI options for `cargo-hax`. The types defines in this module
/// are also used by the driver and the engine.
pub mod cli_options;

/// Type to represent errors, mainly in `hax-engine`. The engine
/// doesn't do any reporting itself: it only sends JSON to its stdout,
/// and `cargo-hax` takes care of reporting everything in a rustc
/// style.
pub mod diagnostics;

/// The types used to communicate between `cargo-hax` and the custom
/// driver.
pub mod driver_api;

/// The types used to communicate between `cargo-hax` and
/// `hax-engine`.
pub mod engine_api;

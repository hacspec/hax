# `hax-types`
This crate contains the type definitions that are used to communicate between:
 - the command line (the `cargo-hax` binary);
 - the custom rustc driver;
 - the hax engine (the `hax-engine` binary).
 
Those three component send and receive messages in JSON or CBOR on
stdin and stdout.

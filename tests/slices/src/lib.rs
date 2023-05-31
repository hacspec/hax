#![allow(dead_code)]

// The issue here is probably both, pointer and slice. We first run into the slice.
const VERSION: &[u8] = b"v1";

// This panics
// thread 'rustc' panicked at 'hax-engine exited with non-zero code', cli/driver/src/exporter.rs:217:2
pub fn do_something(_: &[u8]) {}

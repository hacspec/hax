# Tests the whole toolchain

This crate defines a custom test harness[^1][^2] that scans for packages
in the Cargo workspace `../tests/Cargo.toml`.

Each package in that workspace should define a sequence of tests to be
run in the `package.metadata.circus-tests` dictionary of its
`Cargo.toml` manifest.

Note this cargo test is disabled by default, since it requires both
the Cargo and Dune package to be built. To run this test, please use
the command `cargo test --test toolchain`.

## Format for `package.metadata.circus-tests`
`package.metadata.circus-tests` is a map from a target (e.g. `into
fstar` or `lint hacspec`) to a **test specification** (see below).

`package.metadata.circus-tests` is expected to be a **dictionary** with
the following optional fields:
 - `lint`, a map from a **linter name** to a **test specification**.
 - `into`, a map from a **backend name** to a **test specification**.
   
Note that instead of linter or backend names, conjunction are allowed,
for instance `fstar+coq`.
   
### Test specifications
A **test specification** is a dictionary with the following fields:
 - `positive: bool`: is the test positive (i.e. expected to succeed) or negative?
 - `optional: bool`: is the test optional? (useful for slow tests for instance)
 - `broken: bool`: is this test broken because of some feature not being implemented?
 - `issue_id: u64`: when the test has a companion issue on GitHub (closed or not)
 
### Linter names
The available linters can be listed by running `cargo circus lint --help`.

### Backend names
The available backends can be listed by running `cargo circus into --help`.

## The `insta` tool and library
Those tests are written using the [`insta`
library](https://insta.rs/). This allows us to enforce the stability
of `stdout` and `stderr` for negative tests. In the future, we will
also ensure the files produced by the different backends remains the
same in positive tests of extraction.

When some `stderr` changes, one can review (by interactively accepting
or rejecting changes) changes using the [`cargo-insta`
subcommand](https://insta.rs/docs/cli/).


[^1]: https://doc.rust-lang.org/cargo/reference/cargo-targets.html#the-harness-field
[^2]: https://nexte.st/book/custom-test-harnesses.html

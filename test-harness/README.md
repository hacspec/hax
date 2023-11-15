# Tests the whole toolchain

This crate defines a custom test harness[^1][^2] that scans for packages
in the Cargo workspace `../tests/Cargo.toml`.

Each package in that workspace should define a sequence of tests to be
run in the `package.metadata.hax-tests` dictionary of its
`Cargo.toml` manifest.

Note this cargo test is disabled by default, since it requires both
the Cargo and Dune package to be built. To run this test, please use
the command `cargo test --test toolchain`.

## Format for `package.metadata.hax-tests`

`package.metadata.hax-tests` is a map from a target (e.g. `into
fstar` or `lint hacspec`) to a **test specification** (see below).

`package.metadata.hax-tests` is expected to be a **dictionary** with
the following optional fields:

- `lint`, a map from a **linter name** to a **test specification**.
- `into`, a map from a **backend name** to a **test specification**.

Note that instead of linter or backend names, conjunction are allowed,
for instance `fstar+coq`.

### Test specifications

A **test specification** is a dictionary with the following fields:

- <code><b>positive</b>: bool <i>⟨true⟩</i></code>: is the test positive (the exit code of the `cargo hax` command is `0`) or negative (the exit code is non-null)?
- <code><b>snapshots</b></code>: should we enforce the stability of the output of the `cargo hax` command?
  - <code>snapshots.<b>stdout</b>: bool <i>⟨true⟩</i></code>
  - <code>snapshots.<b>stderr</b>: bool <i>⟨true⟩</i></code>  
    **Note:** this field can also be set to the following strings: `stdout`, `stderr`, `both` or `none`.
- <code><b>optional</b>: bool <i>⟨false⟩</i></code>: is the test optional? (useful for slow tests for instance)
- <code><b>broken</b>: bool <i>⟨false⟩</i></code>: is this test broken because of some feature not being implemented?
- <code><b>issue_id</b>: u64 <i>⟨null⟩</i></code>: when the test has a companion issue on GitHub (closed or not)

### Linter names

The available linters can be listed by running `cargo hax lint --help`.

### Backend names

The available backends can be listed by running `cargo hax into --help`.

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

## Miscelaneous
 - If the environment variable `DUNEJOBS` is set, it will set the `-j`
   flag when `dune build`ing, controlling the maximum number of jobs
   `dune build` will run in parallel.

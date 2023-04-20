#!/usr/bin/env bash

set -x -e

# Install the Rust CLI & frontend, providing `cargo-circus` and `driver-circus`:
cargo install --path cli/driver && cargo install --path cli/subcommands

# Install the OCaml engine:
cd engine
opam install --deps-only .
DYLD_LIBRARY_PATH=$(rustup run nightly-2022-12-06 rustc --print=sysroot)/lib dune build
export PATH=$PATH:$PWD/_build/install/default/bin
cd -


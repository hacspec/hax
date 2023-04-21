#!/usr/bin/env bash

set -x -e

# Install the Rust CLI & frontend, providing `cargo-circus` and `driver-circus`:
cargo install --path cli/driver && cargo install --path cli/subcommands

# Install the OCaml engine:
OPAMASSUMEDEPEXTS=1 opam install --yes ./engine

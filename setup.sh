#!/usr/bin/env bash

set -x -e

# Install the Rust CLI & frontend, providing `cargo-hax` and `driver-hax`:
for i in driver subcommands; do
    cargo install --force --path "cli/$i";
done

# Install the OCaml engine:
OPAMASSUMEDEPEXTS=1 opam install --yes ./engine

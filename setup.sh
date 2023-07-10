#!/usr/bin/env bash

set -x -e

ensure_binary_available() {
    command -v "$1" >/dev/null 2>&1 || {
        printf '\e[31mError: binary \e[1m%s\e[0m\e[31m was not found.\e[0m\n' "$1"
        printf '\e[37m(Did you look at \e[1mManual installation\e[0m\e[37m in \e[1mREADME.md\e[0m\e[37m?)\e[0m.\n'
        exit 1
    }
}

for binary in opam node rustup jq; do
    ensure_binary_available $binary
done

# Install the Rust CLI & frontend, providing `cargo-hax` and `driver-hax`:
for i in driver subcommands; do
    cargo install --force --path "cli/$i";
done

# Install the OCaml engine:
OPAMASSUMEDEPEXTS=1 opam install --yes ./engine

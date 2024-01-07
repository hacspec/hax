#!/usr/bin/env bash

set -eu

opam_jobs=2

# Parse command line arguments.
all_args=("$@")
while [ $# -gt 0 ]; do
    case "$1" in
    -j)
        opam_jobs=$2
        shift
        ;;
    esac
    shift
done

# Ensures a given binary is available in PATH
ensure_binary_available() {
    command -v "$1" >/dev/null 2>&1 || {
        printf '\e[31mError: binary \e[1m%s\e[0m\e[31m was not found.\e[0m\n' "$1"
        printf '\e[37m(Did you look at \e[1mManual installation\e[0m\e[37m in \e[1mREADME.md\e[0m\e[37m?)\e[0m.\n'
        exit 1
    }
}

# Installs the Rust CLI & frontend, providing `cargo-hax` and `driver-hax`
install_rust_binaries() {
    for i in driver subcommands; do
        (
            set -x
            cargo install --force --path "cli/$i"
        )
    done
}

# Provides the `hax-engine` binary
install_ocaml_engine() {
    # Fixes out of memory issues (https://github.com/hacspec/hax/issues/197)
    {
        # Limit the number of thread spawned by opam
        export OPAMJOBS=$opam_jobs
        # Make the garbadge collector of OCaml more agressive (see
        # https://discuss.ocaml.org/t/how-to-limit-the-amount-of-memory-the-ocaml-compiler-is-allowed-to-use/797)
        export OCAMLRUNPARAM="o=20"
    }
    # Make opam show logs when an error occurs
    export OPAMERRLOGLEN=0
    # Make opam ignore system dependencies (it doesn't handle properly certain situations)
    export OPAMASSUMEDEPEXTS=1
    (
        set -x
        opam uninstall hax-engine || true
        opam install --yes ./engine
    )
}

for binary in opam node rustup jq; do
    ensure_binary_available $binary
done
install_rust_binaries
install_ocaml_engine

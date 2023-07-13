#!/usr/bin/env bash

set -eu

# Check if the path is correctly set
check_PATH() {
    for path in .cargo/bin
    do
        if [[ ! ":$PATH:" == *":$HOME/$path:"* ]]; then
            printf '\e[33mWarning: your path is missing \e[1m~/%s\e[0m\e[33m, you might want to add it.\e[0m\n' "$path"
        fi
    done
}

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
        ( set -x; cargo install --force --path "cli/$i")
    done
}

# Provides the `hax-engine` binary
install_ocaml_engine() {
    # Fixes out of memory issues (https://github.com/hacspec/hacspec-v2/issues/197)
    {
        # Limit the number of thread spawned by opam
        export OPAMJOBS=2
        # Make the garbadge collector of OCaml more agressive (see
        # https://discuss.ocaml.org/t/how-to-limit-the-amount-of-memory-the-ocaml-compiler-is-allowed-to-use/797)
        export OCAMLRUNPARAM="o=20"
    }
    # Make opam show logs when an error occurs
    export OPAMERRLOGLEN=0
    # Make opam ignore system dependencies (it doesn't handle properly certain situations)
    export OPAMASSUMEDEPEXTS=1
    (set -x; opam install --yes ./engine)
}

# Install backends
install_backends() {
    HAX_BACKENDS_DIR=${HAX_BACKENDS_DIR:-"$HOME/.hax"}
    rm -rf "$HAX_BACKENDS_DIR"
    cp -rf ./backends "$HAX_BACKENDS_DIR"
}

for binary in opam node rustup jq; do
    ensure_binary_available $binary
done
install_rust_binaries
install_ocaml_engine
install_backends
check_PATH

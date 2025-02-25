#!/usr/bin/env bash

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )
cd "$SCRIPT_DIR/.."

RUSTC_CHECKOUT="$(pwd)/rustc"

COMMIT=$(rustc --version --verbose | sed -n 's|commit-hash: ||p')
HOST=$(rustc --version --verbose | sed -n 's|host: ||p')

echo "COMMIT=$COMMIT"
echo "HOST=$HOST"

init_rustc_repo() {
    mkdir -p "$RUSTC_CHECKOUT"
    cd "$RUSTC_CHECKOUT"
    git init
    git remote add origin https://github.com/rust-lang/rust.git
    cd -
}

checkout_commit() {
    git fetch origin "$COMMIT"
    git reset --hard "$COMMIT"
    git submodule update --init --recursive
}

if [[ ! -d "$RUSTC_CHECKOUT" ]]; then
    init_rustc_repo
fi

cd "$RUSTC_CHECKOUT"

checkout_commit

./x.py build
cd library/core/

export HAX_RUSTFMT=no
export HAX_CORE_EXTRACTION_MODE=on
export HAX_VANILLA_RUSTC=never
export RUSTUP_TOOLCHAIN="nightly-2024-10-23"
export RUSTFLAGS='--cfg bootstrap'

cargo hax -C -Z build-std=core --target "$HOST" \; "$@"

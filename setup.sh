#!/usr/bin/env bash

set -x -e

cd thir-export
cargo install --path cli
cd -

cd thir-elab
opam install --deps-only .
DYLD_LIBRARY_PATH=$(rustup run nightly-2022-12-06 rustc --print=sysroot)/lib dune build
export PATH=$PATH:$PWD/_build/install/default/bin
cd -


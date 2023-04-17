#!/usr/bin/env bash

set -x -e

cargo install --path cli

cd engine
opam install --deps-only .
DYLD_LIBRARY_PATH=$(rustup run nightly-2022-12-06 rustc --print=sysroot)/lib dune build
export PATH=$PATH:$PWD/_build/install/default/bin
cd -


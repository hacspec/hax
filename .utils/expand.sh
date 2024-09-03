#!/usr/bin/env bash

# This script expands a crate so that one can inspect macro expansion
# by hax. It is a wrapper around `cargo expand` that inject the
# required rustc flags.

RUSTFLAGS='-Zcrate-attr=register_tool(_hax) -Zcrate-attr=feature(register_tool) --cfg hax_compilation --cfg _hax --cfg hax --cfg hax_backend_fstar --cfg hax' cargo expand "$@"


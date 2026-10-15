# Extract the `client_test` crate, using core-models as a dependency.
# This tests the setup an actual user would have.

HAX ?= cargo hax
LEAN_DIR = proofs/lean
EXTRACTION_DIR = $(LEAN_DIR)/ClientTest/

# std's slice-iterator macros OVERRIDE `Iterator::find` (library/core/src/slice/
# iter/macros.rs), and that override's signature has a higher-ranked lifetime
# constrained by a free one, which aeneas cannot translate ("found an occurrence
# of a lifetime constraint relating a higher-ranked lifetime to a free
# lifetime"). Building the slice-`Iter` dictionary that any chained adapter
# needs — `x.iter().map(f)`, `x.iter().rev()` — drags the override in, so
# without this exclude every adapter chain over a slice fails to extract.
#
# Dropping the override is sound: like std's other `Iterator` overrides on
# slices it is a performance specialisation, observationally equal to the
# provided body, and `find` then resolves to our `Iterator::find` shim in
# `CoreModels/Core/FunsEpilogue.lean`.
CHARON_ARGS = --exclude 'core::slice::iter::{impl core::iter::traits::iterator::Iterator for core::slice::iter::Iter<_>}::find'

.PHONY: all extract build clean

all: build

# 1. Extract Rust -> Lean
extract:
	$(HAX) into lean --charon-args="$(CHARON_ARGS)"

# 2. Build the Lean library — this is the actual test.
build: extract
	cd $(LEAN_DIR) && lake exe cache get && lake build

# Remove the generated files; keep the hand-written project files
# (lakefile.toml, lean-toolchain, ClientTest.lean).
clean:
	rm -rf $(EXTRACTION_DIR)
	rm -rf $(LEAN_DIR)/llbc $(LEAN_DIR)/.lake
	rm -f $(LEAN_DIR)/.gitignore

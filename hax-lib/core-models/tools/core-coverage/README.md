# core-coverage

Generates [`COVERAGE.md`](../../COVERAGE.md): a per-module report of how much of
the real `core` / `alloc` public API the model crates provide.

```sh
make coverage          # regenerate COVERAGE.md + coverage.json
```

The report is **not** verified in CI: the numerator is rustdoc JSON of the
model crates, whose `hax-lib` proc-macro expansion is not bit-reproducible
across machines (it emits a few phantom items), so a rebuild-and-diff gate
would be flaky. Treat `COVERAGE.md` as an approximate, periodically-refreshed
snapshot — run `make coverage` when you want current numbers (it also runs as
part of the default `make` target).

## Why rustdoc JSON

"How much of core do we model" is a **source-level, tool-agnostic** question, so
this tool does not use charon. Instead it compares two rustdoc JSON files:

- **numerator** — the model crates, via `cargo +nightly rustdoc --output-format
  json --document-private-items`.
- **denominator** — the real `core`/`alloc`, from the prebuilt `rust-docs-json`
  rustup component (`$(rustc --print sysroot)/share/doc/rust/json/`);

Both must come from the **same nightly** so their `format_version` agrees.
`--document-private-items` is required because the model puts almost everything
in *private* modules (only `vec` is `pub mod`), which charon/aeneas extract
regardless of visibility.

## What is counted

The "API surface", attributed to its **top-level module**:

- module-level items: `fn` / `struct` / `enum` / `union` / `trait` /
  `constant` / `type_alias` / `macro` / `proc_macro` / `trait_alias`;
- inherent methods (impl with no trait), keyed `Type::method`;
- trait-definition methods, keyed `Trait::method`.

Derived trait-impl methods (`impl Clone for T`, `Debug`, `From`, …) and
auto/blanket impls are **not** counted — they are boilerplate, not API to model.

Matching is by `(top-level module, leaf key)` and is **crate-root agnostic**, so
the flat model layout lines up with real core's deep nesting:
`core::iter::traits::iterator::Iterator::next` and the model's
`core_models::iter::…::Iterator::next` both bucket under `iter` with key
`Iterator::next`.

Two subtleties the walker handles:
- **re-exports** — real `core::iter`/`ops` expose their whole API via `pub use`
  from private submodules, so `use` items are followed to their targets;
- **dedup** — each item is counted once, in the first (canonical) module that
  reaches it, and pure re-export aggregators (`prelude`) are skipped, so
  re-exports don't inflate or misattribute the denominator.

## Model naming workarounds (`MODEL_OWNER_ALIASES`)

The model spells some owners differently from core: primitive methods hang off
stand-in types (`Slice`, `Array`), and trait default methods live in companion
traits (`IteratorMethods`, `Neq`, ...), as hax does not support trait defaults.
`MODEL_OWNER_ALIASES` maps these back to core's
names, additively. Extend it when you add a companion trait or a stand-in type.

## Scoping (the tiered report)

`OUT_OF_SCOPE` in `coverage.py` lists modules a pure-Rust verification model is
not trying to provide (`intrinsics`, `arch`, `simd`, `sync`, `os`, `ffi`,
`net`, `time`, `random`, async, …). These are reported in a collapsed
"out-of-scope" section with their own subtotal; the headline percentage is over
the **targeted** modules only. Edit `OUT_OF_SCOPE` to re-scope.

## Notes / limitations

- The numerator is `core_models` + `alloc` only; `rust_primitives` is **not**
  counted. The model uses `rust_primitives` internally, so anything genuinely
  modeled surfaces as a `core_models` item. A module that reads low (e.g.
  `slice`, `str`) honestly reflects that those ops aren't exposed at the
  core-mirroring level.
- Coverage is by item *name/signature presence*, not behavioural correctness —
  that is what `tests/rust_lean_equiv_test/` is for.
- The numbers are approximate: the model's rustdoc JSON depends on `hax-lib`
  proc-macro expansion, which varies slightly across machines (a handful of
  phantom items), so the report can differ by a few items between regenerations
  on different hosts. This is why it is a committed snapshot rather than a
  CI-enforced invariant.

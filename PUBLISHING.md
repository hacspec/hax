# Publishing

## OCaml

There is only the package `hax-engine`, that includes a binary and a
number of libraries.

## Rust

This repository is divided into several crates, some to be published,
some not. All crates should start with the `hax-` prefix, but
`cargo-hax` which is the entrypoint to the cargo `hax` subcommand.

Here is the list of the crates in this repository (excluding `tests`
and `examples`):

- `hax-test-harness` **(doesn't need to be published)**

### cargo-hax

1. `hax-frontend-exporter-options` (`frontend/exporter/options `)
2. `hax-adt-into` (`frontend/exporter/adt-into`)
3. `hax-frontend-exporter` (`frontend/exporter`)
4. `hax-types` (`hax-types`)
5. `hax-subcommands` (binaries) (`cli/subcommands`)
   - `cargo-hax`
   - `hax-export-json-schemas`
   - `hax-pretty-print-diagnostics`

- `hax-driver`

### hax-lib

We publish the following crates that are helper libraries to be used
for hax code:

1. `hax-lib-macros-types`
2. `hax-lib-macros`
3. `hax-lib`

### Supporting crates for the engine
The crate listed below are used only by the OCaml build of the
engine. Those should not be published on `crate.io`.

1. `cargo-hax-engine-names`
2. `cargo-hax-engine-names-extract`

## Procedure
 1. Bump the version number with `cargo release LEVEL --no-publish --execute` (`cargo release --help` for more details on `LEVEL`). This will bump the version of every Rust crate, but also the version in `engine/dune-project`. This will also regenerate `engine/hax-engine.opam`. Note this will *not* publish the crate.
 2. PR the change
 3. when the PR is merged in main, checkout `main` and run `cargo release --execute`

Note: for now, we are not publishing to Opam. Instead, let's just advertise the following for installation:
```bash
opam pin hax-engine https://github.com/hacspec/hax.git#the-release-tag
opam install hax-engine
```

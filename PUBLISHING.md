# Crates publishing

This repository is divided into several crates, some to be published,
some not. All crates should start with the `hax-` prefix, but
`cargo-hax` which is the entrypoint to the cargo `hax` subcommand.

Here is the list of the crates in this repository (excluding `tests`
and `examples`):

- `hax-test-harness` **(doesn't need to be published)**
- `hax-lib-macros`
- `hax-lint`
- `hax-frontend-exporter-options`
- `hax-adt-into`
- `hax-frontend-exporter`
- `hax-diagnostics`
- `hax-phase-debug-webapp`
- `hax-subcommands` (binaries)
  - `cargo-hax`
  - `hax-export-json-schemas`
  - `hax-pretty-print-diagnostics`
- `hax-cli-options-engine`
- `hax-cli-options`
- `hax-driver`




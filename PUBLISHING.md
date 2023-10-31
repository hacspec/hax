# Crates publishing

This repository is divided into several crates, some to be published,
some not. All crates should start with the `hax-` prefix, but
`cargo-hax` which is the entrypoint to the cargo `hax` subcommand.

Here is the list of the crates in this repository (excluding `tests`
and `examples`):

- `hax-test-harness` **(doesn't need to be published)**
1. `hax-frontend-exporter-options` (`frontend/exporter/options `)
2. `hax-adt-into` (`frontend/exporter/adt-into`)
3. `hax-frontend-exporter` (`frontend/exporter`)
4. `hax-cli-options` (`cli/options`)
5. `hax-diagnostics` (`frontend/diagnostics`)
6. `hax-cli-options-engine` (`cli/options/engine`)
7. `hax-subcommands` (binaries) (`cli/subcommands`)
    - `cargo-hax`
    - `hax-export-json-schemas`
    - `hax-pretty-print-diagnostics`
- `hax-lib-macros`
- `hax-lint`
- `hax-phase-debug-webapp`
- `hax-driver`




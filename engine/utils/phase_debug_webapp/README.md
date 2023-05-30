This folder implements a small webapp designed for viewing how a rust
crate is translated by the engine, step-by-step.

The engine works by phases. First, it receives a tweaked version of
Rust's internal typed representation. On this representation, the
engine then applies sequentially a certain number of phases. Each
phase transports your code from a representation to another, by
performing some translation or rewriting.

This webapp allows you to display a rust code before and after each
phase.

### How to
When running `cargo hax into BACKEND`, pass the option
`--debug-engine DEBUG_DIRECTORY` to the subcommand `into`, with
`DEBUG_DIRECTORY` an existing directory of your choice. For instance,
`DEBUG_DIRECTORY` could be `/tmp/something`.

Then, just run `./server.js DEBUG_DIRECTORY`: and browse the URL
displayed in your terminal with your web browser.


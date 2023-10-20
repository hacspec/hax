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
`--debug-engine` (or `-d`) to the subcommand `into`. This will spawn a
small webserver with the webapp.


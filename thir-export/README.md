# Thir-Export

Given a Rust crate, simplifies then exports its THIR to a JSON file.

## Usage
`cargo thir-export [THIR-EXPORT-OPTIONS] [-- [CARGO-BUILD-OPTIONS]]`

For example, `cargo thir-export -o file.json -- -p mycrate` will read the crate `mycrate`, and export a JSON file `file.json`.


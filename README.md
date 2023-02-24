# Hacspec v2

## Structure of this repository
 - `thir-export/`: a [cargo subcommand](https://doc.rust-lang.org/book/ch14-05-extending-cargo.html) that exports the [**THIR**](https://rustc-dev-guide.rust-lang.org/thir.html) abstract syntax tree of a given crate into **THIR'** (a simplified THIR) as a JSON file. See [`thir-export/README.md`](./thir-export/README.md) for more details.
 - `thir-json-visualizer/`: a quick & dirty React web app to browse *THIR'* JSON files.
 - `thir-elab/`: a program that eats THIR' as JSON and that converts into an OCaml AST. That AST is parametrized by *features* (e.g. is *mutation* allowed? are *loops* allowed? etc.). Then, `thir-elab` offers a set of desugaring steps to, basically, lower THIR' to match F*/Coq/EasyCrypt/… feature set. Ultimately, we want to have backends that (1) ask for a certain desugar level and (2) produce code in F*/Coq/EasyCrypt/…
 - `ocaml_of_json_schema.js`: a quick & dirty script that translates a [JSON Schema](https://json-schema.org/) into OCaml types and serializers. *(note: this will be replaced by [quicktype](https://github.com/quicktype/quicktype) when we our OCaml backend is ready)*

## Quick start
### With Nix
**Prerequisites:** install the [Nix package manager](https://nixos.org/) with flake support: https://github.com/mschwaig/howto-install-nix-with-flake-support

#### Get the _THIR'_ JSON out of a crate
1. `cd path/to/your/crate`
2. `nix run github:w95psp/hacspec-v2#thir-export`  
    ...will create `thir_export.json` in the current directory.
    
**More generally:** `nix run github:w95psp/hacspec-v2#thir-export -- THIR-EXPORT-ARGUMENTS -- CARGO-ARGUMENTS`; for instance `CARGO-ARGUMENTS` could be `-p crate-name`.


#### Running `thir-elab` on the JSON
1. `nix run github:w95psp/hacspec-v2#thir-elab /path/to/thir_export.json`

#### Visualization of the THIR' JSON
1. `cd /directory/in/which/the/thir_export.json/file/lives/`
2. `nix run github:w95psp/hacspec-v2#thir-json-visualizer`
3. visit `http://localhost:8888/`

### Without Nix
For now, the OCaml part is a bit hard to get it compiled without Nix since it's relying on a (not yet merged) F* branch.

The Rust part should be fine though, it should only be a matter of `cargo build`.

## Edit the sources (Nix)
Just clone & `cd` into the repo, then run `nix develop .#target` –target being `thir-export` or `thir-elab`.
You can also just use [direnv](https://github.com/nix-community/nix-direnv), with [editor integration](https://github.com/direnv/direnv/wiki#editor-integration).


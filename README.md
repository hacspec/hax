# Hacspec v2

## Quick start with Nix (works on [Linux](https://nixos.org/download.html#nix-install-linux), [MacOS](https://nixos.org/download.html#nix-install-macos) and [Windows](https://nixos.org/download.html#nix-install-windows))

<details>
  <summary><b>Prerequisites:</b> <a href="https://nixos.org/">Nix package
manager</a> <i>(with <a href="https://nixos.wiki/wiki/Flakes">flakes</a> enabled)</i></summary>

  - Either using the [Determinate Nix Installer](https://github.com/DeterminateSystems/nix-installer), with the following bash one-liner:
    ```bash
    curl --proto '=https' --tlsv1.2 -sSf -L https://install.determinate.systems/nix | sh -s -- install
    ```
  - or following [those steps](https://github.com/mschwaig/howto-install-nix-with-flake-support).

</details>

### Get the F\* translation of a crate

1. `cd path/to/your/crate`
2. `nix run github:hacspec/hacspec-v2#circus -o some/output/dir fstar`  
   will create `fst` modules in directory `some/output/dir`.

### Get a shell with `cargo circus`, `cargo thir-export` and `thir-elab`

1. `nix develop github:hacspec/hacspec-v2`

<details>
  <summary>Other operations</summary>
  
#### Get the _THIR'_ JSON out of a crate
1. `cd path/to/your/crate`
2. `nix run github:hacspec/hacspec-v2#thir-export`  
    ...will create `thir_export.json` in the current directory.
    
**More generally:** `nix run github:hacspec/hacspec-v2#thir-export -- THIR-EXPORT-ARGUMENTS`. Replace `THIR-EXPORT-ARGUMENTS` with `--help` to get more information.

#### Running `thir-elab` on the JSON

1. `nix run github:hacspec/hacspec-v2#thir-elab -i /path/to/thir_export.json`

#### Visualization of the THIR' JSON

1. `cd /directory/in/which/the/thir_export.json/file/lives/`
2. `nix run github:hacspec/hacspec-v2#thir-json-visualizer`
3. visit `http://localhost:8888/`

</details>

## Without Nix

1. Make sure to have the following installed on your system:

- `opam` (`opam switch create 4.14.1`)
- `rustup`
- `nodejs`
- `python2.7` (for example using [pyenv](https://github.com/pyenv/pyenv))

2. Clone this repo `git clone git@github.com:hacspec/hacspec-v2.git`
3. Install `thir-export`:
   1. `cd thir-export`
   2. `cargo install --path cli`
4. Build `thir-elab`:
   1. `cd thir-elab`
   2. `opam install --deps-only .`
   3. `dune build`
   4. add the subfolder `_build/install/default/bin` in your `PATH`
5. Commands available are:
   - `cargo circus [--help]`: export a crate to a backend (F\* for instance);
   - `cargo thir-export [--help]`: export the THIR of a crate to a JSON file;
   - `thir-elab [--help]`: takes the THIR JSON export of a crate and outputs F\*/... code.

The librustc library path needs to be added to `DYLD_LIBRARY_PATH=$(rustc --print=sysroot)/lib`
Make sure to use the right Rust nightly version, which is currently `nightly-2022-12-06`.

> **Note**
> Please use and check the [setup.sh](./setup.sh) for these steps as well.

## Edit the sources (Nix)

Just clone & `cd` into the repo, then run `nix develop .#target` –target being `thir-export` or `thir-elab`.
You can also just use [direnv](https://github.com/nix-community/nix-direnv), with [editor integration](https://github.com/direnv/direnv/wiki#editor-integration).

## Structure of this repository

- `thir-export/`: a [cargo subcommand](https://doc.rust-lang.org/book/ch14-05-extending-cargo.html) that exports the [**THIR**](https://rustc-dev-guide.rust-lang.org/thir.html) abstract syntax tree of a given crate into **THIR'** (a simplified THIR) as a JSON file. See [`thir-export/README.md`](./thir-export/README.md) for more details.
- `thir-json-visualizer/`: a quick & dirty React web app to browse _THIR'_ JSON files.
- `thir-elab/`: a program that eats THIR' as JSON and that converts into an OCaml AST. That AST is parametrized by _features_ (e.g. is _mutation_ allowed? are _loops_ allowed? etc.). Then, `thir-elab` offers a set of desugaring steps to, basically, lower THIR' to match F*/Coq/EasyCrypt/… feature set. Ultimately, we want to have backends that (1) ask for a certain desugar level and (2) produce code in F*/Coq/EasyCrypt/…
- `ocaml_of_json_schema.js`: a quick & dirty script that translates a [JSON Schema](https://json-schema.org/) into OCaml types and serializers. _(note: this will be replaced by [quicktype](https://github.com/quicktype/quicktype) when we our OCaml backend is ready)_

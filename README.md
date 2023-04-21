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

+ Run circus on a crate to get F\*/Coq/...:
   - `cd path/to/your/crate`
   - `nix run github:hacspec/hacspec-v2 -- -o some/output/dir fstar`  
      will create `fst` modules in directory `some/output/dir`.  
      *Note: replace `fstar` by your backend of choice*

+ Install the tool:  `nix profile install github:hacspec/hacspec-v2`
   - then run `cargo circus --help` anywhere

## Using Docker
1. Clone this repo: `git clone git@github.com:hacspec/hacspec-v2.git && cd hacspec-v2`
3. Build the docker image: `docker build -f .docker/Dockerfile . -t hacspec-v2`
4. Get a shell: `docker run -it --rm -v /some/dir/with/a/crate:/work hacspec-v2 bash`
5. You can now run `cargo-circus --help` (notice here we use `cargo-circus` instead of `cargo circus`)

## Manual installation

1. Make sure to have the following installed on your system:

- `opam` (`opam switch create 4.14.1`)
- `rustup`
- `nodejs`

2. Clone this repo: `git clone git@github.com:hacspec/hacspec-v2.git && cd hacspec-v2`
3. Run the [setup.sh](./setup.sh) script: `./setup.sh`.
4. Run `cargo-circus --help`

The librustc library path needs to be added to `DYLD_LIBRARY_PATH=$(rustc --print=sysroot)/lib`
Make sure to use the right Rust nightly version, which is currently `nightly-2022-12-06`.

## Edit the sources (Nix)

Just clone & `cd` into the repo, then run `nix develop .`.
You can also just use [direnv](https://github.com/nix-community/nix-direnv), with [editor integration](https://github.com/direnv/direnv/wiki#editor-integration).

## Structure of this repository

- `rust-frontend/`: Rust library that hooks in the rust compiler and
  extract its internal typed abstract syntax tree
  [**THIR**](https://rustc-dev-guide.rust-lang.org/thir.html) as JSON.
- `engine/`: the simplication and elaboration engine that translate
  programs from the Rust language to various backends (see `engine/backends/`).
- `cli/`: the `circus` subcommand for Cargo.

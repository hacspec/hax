# Hax

## Usage
Hax is a cargo subcommand. 
The command `cargo hax` accepts the following subcommands:
 * **`into`** (`cargo hax into BACKEND`): translate a Rust crate to the backend `BACKEND` (e.g. `fstar`, `coq`).
 * **`lint`** (`cargo hax lint LINTER`): lint a Rust crate with `LINTER`.
 * **`json`** (`cargo hax json`): extract the typed AST of your crate as a JSON file.
 
Note:
 * `BACKEND` can be `fstar`, `coq` or `easycrypt`. The list of
   supported backends can be displayed running `cargo hax into
   --help`.
 * `LINTER` can be:
   * `hacspec`: is your Rust code in the Hacspec subset, that is, a simple enough subset of Rust suited for specifications? (TODO: documentation)
   * `rust`: checks *fast* whether your code will be extractible to `fstar` or `coq` without running the full toolchain? (running the full toolchain is not fast enough for LSPs for instance)
 * The subcommand `cargo hax` takes options, list them with `cargo hax --help`.
 * The subcommand `cargo hax into` takes also options, list them with `cargo hax into --help`.

## Installation
### Nix (works on [Linux](https://nixos.org/download.html#nix-install-linux), [MacOS](https://nixos.org/download.html#nix-install-macos) and [Windows](https://nixos.org/download.html#nix-install-windows))

<details>
  <summary><b>Prerequisites:</b> <a href="https://nixos.org/">Nix package
manager</a> <i>(with <a href="https://nixos.wiki/wiki/Flakes">flakes</a> enabled)</i></summary>

  - Either using the [Determinate Nix Installer](https://github.com/DeterminateSystems/nix-installer), with the following bash one-liner:
    ```bash
    curl --proto '=https' --tlsv1.2 -sSf -L https://install.determinate.systems/nix | sh -s -- install
    ```
  - or following [those steps](https://github.com/mschwaig/howto-install-nix-with-flake-support).

</details>

+ Run hax on a crate to get F\*/Coq/...:
   - `cd path/to/your/crate`
   - `nix run github:hacspec/hacspec-v2 -- into fstar`  
      will create `fst` modules in the directory `hax/extraction/fstar`.  
      *Note: replace `fstar` by your backend of choice*

+ Install the tool:  `nix profile install github:hacspec/hacspec-v2`
   - then run `cargo hax --help` anywhere

### Using Docker
1. Clone this repo: `git clone git@github.com:hacspec/hacspec-v2.git && cd hacspec-v2`
3. Build the docker image: `docker build -f .docker/Dockerfile . -t hacspec-v2`
4. Get a shell: `docker run -it --rm -v /some/dir/with/a/crate:/work hacspec-v2 bash`
5. You can now run `cargo-hax --help` (notice here we use `cargo-hax` instead of `cargo hax`)

### Manual installation

1. Make sure to have the following installed on your system:

- `opam` (`opam switch create 4.14.1`)
- `rustup`
- `nodejs`
- `jq`

2. Clone this repo: `git clone git@github.com:hacspec/hacspec-v2.git && cd hacspec-v2`
3. Run the [setup.sh](./setup.sh) script: `./setup.sh`.
4. Run `cargo-hax --help`

The librustc library path needs to be added to `DYLD_LIBRARY_PATH=$(rustc --print=sysroot)/lib`
Make sure to use the right Rust nightly version (see [`rust-toolchain.toml`](./rust-toolchain.toml)).

## Hacking on Hax
### Edit the sources (Nix)

Just clone & `cd` into the repo, then run `nix develop .`.
You can also just use [direnv](https://github.com/nix-community/nix-direnv), with [editor integration](https://github.com/direnv/direnv/wiki#editor-integration).

### Structure of this repository

- `rust-frontend/`: Rust library that hooks in the rust compiler and
  extract its internal typed abstract syntax tree
  [**THIR**](https://rustc-dev-guide.rust-lang.org/thir.html) as JSON.
- `engine/`: the simplication and elaboration engine that translate
  programs from the Rust language to various backends (see `engine/backends/`).
- `cli/`: the `hax` subcommand for Cargo.

---
weight: -5
---

# Introduction

hax is a tool for high assurance translations of a large subset of
Rust into formal languages such as [F\*](https://www.fstar-lang.org/) or [Rocq](https://rocq-prover.org/).

## Usage

Hax is a cargo subcommand. 
The command `cargo hax` accepts the following subcommands:

* **`into`** (`cargo hax into BACKEND`): translate a Rust crate to the backend `BACKEND` (e.g. `fstar`, `coq`).
* **`json`** (`cargo hax json`): extract the typed AST of your crate as a JSON file.
 
Note:

* `BACKEND` can be `fstar`, `coq`, `easycrypt` or `pro-verif`. `cargo hax into --help`
   gives the full list of supported backends.
* The subcommands `cargo hax`, `cargo hax into` and `cargo hax into
   <BACKEND>` takes options. For instance, you can `cargo hax into
   fstar --z3rlimit 100`. Use `--help` on those subcommands to list
   all options.

## Installation

### Manual installation

1. Make sure to have the following installed on your system:

      - [`opam`](https://opam.ocaml.org/) (`opam switch create 5.1.1`)
      - [`rustup`](https://rustup.rs/)
      - [`nodejs`](https://nodejs.org/)
      - [`jq`](https://jqlang.github.io/jq/)

2. Clone this repo: `git clone git@github.com:hacspec/hax.git && cd hax`
3. Run the [setup.sh](./setup.sh) script: `./setup.sh`.
4. Run `cargo-hax --help`

### Nix

This should work on [Linux](https://nixos.org/download.html#nix-install-linux), [MacOS](https://nixos.org/download.html#nix-install-macos) and [Windows](https://nixos.org/download.html#nix-install-windows).

<b>Prerequisites:</b> <a href="https://nixos.org/">Nix package
manager</a> <i>(with <a href="https://nixos.wiki/wiki/Flakes">flakes</a> enabled)</i>

  - Either using the [Determinate Nix Installer](https://github.com/DeterminateSystems/nix-installer), with the following bash one-liner:
    ```bash
    curl --proto '=https' --tlsv1.2 -sSf -L https://install.determinate.systems/nix | sh -s -- install
    ```
  - or following [those steps](https://github.com/mschwaig/howto-install-nix-with-flake-support).

+ **Run hax on a crate directly** to get F\*/Coq/... (assuming you are in the crate's folder):
   - `nix run github:hacspec/hax -- into fstar` extracts F*.

+ **Install hax**:  `nix profile install github:hacspec/hax`, then run `cargo hax --help` anywhere
+ **Note**: in any of the Nix commands above, replace `github:hacspec/hax` by `./dir` to compile a local checkout of hax that lives in `./some-dir`
+ **Setup binary cache**: [using Cachix](https://app.cachix.org/cache/hax), just `cachix use hax`

### Docker

1. Clone this repo: `git clone git@github.com:hacspec/hax.git && cd hax`
2. Build the docker image: `docker build -f .docker/Dockerfile . -t hax`
3. Get a shell: `docker run -it --rm -v /some/dir/with/a/crate:/work hax bash`
4. You can now run `cargo-hax --help` (notice here we use `cargo-hax` instead of `cargo hax`)

Note: Please make sure that `$HOME/.cargo/bin` is in your `$PATH`, as
that is where `setup.sh` will install hax.


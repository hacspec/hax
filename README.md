# Hax

hax is a tool for high assurance translations that translates a large subset of
Rust into formal languages such as [F\*](https://www.fstar-lang.org/) or [Coq](https://coq.inria.fr/).
This extends the scope of the hacspec project, which was previously a DSL embedded in Rust,
to a usable tool for verifying Rust programs.

> So what is hacspec now?

hacspec is the functional subset of Rust that can be used, together with a hacspec
standard library, to write succinct, executable, and verifiable specifications in
Rust.
These specifications can be translated into formal languages with hax.

## Usage
Hax is a cargo subcommand. 
The command `cargo hax` accepts the following subcommands:
 * **`into`** (`cargo hax into BACKEND`): translate a Rust crate to the backend `BACKEND` (e.g. `fstar`, `coq`).
 * **`json`** (`cargo hax json`): extract the typed AST of your crate as a JSON file.
 
Note:
 * `BACKEND` can be `fstar`, `coq` or `easycrypt`. The list of
   supported backends can be displayed running `cargo hax into
   --help`.
 * The subcommand `cargo hax` takes options, list them with `cargo hax --help`.
 * The subcommand `cargo hax into` takes also options, list them with `cargo hax into --help`.

## Installation
<details>
  <summary><b>Nix</b></summary>

 This should work on [Linux](https://nixos.org/download.html#nix-install-linux), [MacOS](https://nixos.org/download.html#nix-install-macos) and [Windows](https://nixos.org/download.html#nix-install-windows).

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

</details>

<details>
  <summary><b>Using Docker</b></summary>

1. Clone this repo: `git clone git@github.com:hacspec/hacspec-v2.git && cd hacspec-v2`
3. Build the docker image: `docker build -f .docker/Dockerfile . -t hacspec-v2`
4. Get a shell: `docker run -it --rm -v /some/dir/with/a/crate:/work hacspec-v2 bash`
5. You can now run `cargo-hax --help` (notice here we use `cargo-hax` instead of `cargo hax`)

</details>

<details>
  <summary><b>Manual installation</b></summary>

1. Make sure to have the following installed on your system:

- `opam` (`opam switch create 4.14.1`)
- `rustup`
- `nodejs`
- `jq`

2. Clone this repo: `git clone git@github.com:hacspec/hacspec-v2.git && cd hacspec-v2`
3. Run the [setup.sh](./setup.sh) script: `./setup.sh`.
4. Run `cargo-hax --help`

</details>

## Examples

There's a set of examples that show what hax can do for you.
Please check out the [examples directory](examples/)

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

### Recompiling
You can use the [`.utils/rebuild.sh`](./.utils/rebuild.sh) script (which is available automatically as the command `rebuild` when using the Nix devshell):
 - `rebuild`: rebuild the Rust then the OCaml part;
 - `rebuild TARGET`: rebuild the `TARGET` part (`TARGET` is either `rust` or `ocaml`).

## Publications & Other material

* [📕 Tech report](https://hal.inria.fr/hal-03176482)
* [📕 HACSpec: A gateway to high-assurance cryptography](https://github.com/hacspec/hacspec/blob/master/rwc2023-abstract.pdf)
* [📕 Original hacspec paper](https://www.franziskuskiefer.de/publications/hacspec-ssr18-paper.pdf)

### Secondary literature, using hacspec:
* [📕 Last yard](https://eprint.iacr.org/2023/185)

## Contributing

Before starting any work please join the [Zulip chat][chat-link], start a [discussion on Github](https://github.com/hacspec/hax/discussions), or file an [issue](https://github.com/hacspec/hax/issues) to discuss your contribution.


[chat-link]: https://hacspec.zulipchat.com

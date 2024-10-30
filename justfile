@_default:
  just --list

# Build Rust and OCaml parts and install binaries in PATH. To build
# only OCaml parts or only Rust parts, set target to `rust` or
# `ocaml`.
@build target='rust+ocaml':
  ./.utils/rebuild.sh {{target}}

alias b := build

# alias for `build rust`
@rust:
  just build rust

# alias for `build ocaml`
@ocaml:
  just build ocaml

# `cargo expand` a crate, but sets flags and crate attributes so that the expansion is exactly what hax receives. This is useful to debug hax macros.
[no-cd]
expand *FLAGS:
  RUSTFLAGS='-Zcrate-attr=register_tool(_hax) -Zcrate-attr=feature(register_tool) --cfg hax_compilation --cfg _hax --cfg hax --cfg hax_backend_fstar --cfg hax' cargo expand {{FLAGS}}

# Show the generated module `concrete_ident_generated.ml`, that contains all the Rust names the engine knows about. Those names are declared in the `./engine/names` crate.
@list-names:
  hax-engine-names-extract | sed '/include .val/,$d' | just _pager

# Show the Rust to OCaml generated types available to the engine.
@list-types:
  just _ensure_command_in_path ocamlformat ocamlformat
  cd engine && dune describe pp lib/types.ml \
    | sed -e '1,/open ParseError/ d' \
    | sed '/let rec pp_/,$d' \
    | ocamlformat --impl - \
    | just _pager

# Show the OCaml module `Generated_generic_printer_base`
@show-generated-printer-ml:
  just _ensure_command_in_path ocamlformat ocamlformat
  cd engine && dune describe pp lib/generated_generic_printer_base.ml \
    | ocamlformat --impl - \
    | just _pager


# Format all the code
fmt:
  cargo fmt
  cd engine && dune fmt

# Run hax tests: each test crate has a snapshot, so that we track changes in extracted code. If a snapshot changed, please review them with `just test-review`.
test:
  cargo test --test toolchain

_test:
  CARGO_TESTS_ASSUME_BUILT=1 cargo test --test toolchain

# Review snapshots
test-review: (_ensure_command_in_path "cargo-insta" "Insta (https://insta.rs)")
  cargo insta review

# Serve the book
book: (_ensure_command_in_path "mdbook" "mdBook (https://rust-lang.github.io/mdBook/)")
  cd book && mdbook serve

# Check the coherency between issues labeled `marked-unimplemented` on GitHub and issues mentionned in the engine in the `Unimplemented {issue_id: ...}` errors.
@check-issues:
  just _ensure_command_in_path jq "jq (https://jqlang.github.io/jq/)"
  just _ensure_command_in_path gh "GitHub CLI (https://cli.github.com/)"
  just _ensure_command_in_path rg "ripgrep (https://github.com/BurntSushi/ripgrep)"
  just _ensure_command_in_path sd "sd (https://github.com/chmln/sd)"
  diff -U0 \
      <(gh issue -R hacspec/hax list --label 'marked-unimplemented' --json number,closed -L 200 \
           | jq '.[] | select(.closed | not) | .number' | sort -u) \
      <(rg 'issue_id:(\d+)' -Ior '$1' | sort -u) \
      | rg '^[+-]\d' \
      | sd '[-](\d+)' '#$1\t is labeled `marked-unimplemented`, but was not found in the code' \
      | sd '[+](\d+)' '#$1\t is *not* labeled `marked-unimplemented` or is closed'

# Check that the licenses of every crate and every package are compliant with `deny.toml`
check-licenses:
  #!/usr/bin/env bash
  just _ensure_command_in_path cargo-deny "cargo-deny (https://embarkstudios.github.io/cargo-deny/)"
  just _ensure_command_in_path toml2json "toml2json (https://github.com/woodruffw/toml2json)"
  echo "> Check licenses for Rust"
  cargo deny check licenses
  cd engine
  echo "> Check licenses for OCaml"
  # initialize opam if needed
  opam env >& /dev/null || opam init --no
  # pin package `hax-engine` if needed
  opam list --required-by=hax-engine --column=name,license: -s >& /dev/null || opam pin . --yes
  # Check that every pacakge matches licenses of `deny.toml`
  if opam list --required-by=hax-engine --column=name,license: -s \
     | grep -Pvi $(toml2json ../deny.toml| jq '.licenses.allow | join("|")'); then
     echo "Some licenses were non compliant to our policy (see `deny.toml`)"
  else
    echo "licenses ok"
  fi

_ensure_command_in_path BINARY NAME:
  #!/usr/bin/env bash
  command -v {{BINARY}} &> /dev/null || {
     >&2 echo -e "\033[0;31mSorry, the binary \033[1m{{BINARY}}\033[0m\033[0;31m is required for this command.\033[0m"
     >&2 echo -e "  \033[0;31m→ please install \033[1m{{NAME}}\033[0m"
     >&2 echo ""
     exit 1
  }

_pager:
  #!/usr/bin/env bash
  if command -v bat &> /dev/null; then
      bat -l ml
  else
      less
  fi

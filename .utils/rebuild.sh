#!/usr/bin/env bash

# This is a small script to rebuild Hax (the Rust CLI & frontend and
# OCaml engine) quickly.

# Options:
#  - the flag `--online` allow Cargo to look for updates on the internet;
#  - the environment variable `DUNEJOBS` limits the number of jobs `dune`
#    is allowed to spawn in parallel while building.

set -euo pipefail

OFFLINE_FLAG="--offline"
if [[ "${1:-}" == "--online" ]]; then
    OFFLINE_FLAG=""
    shift 1
fi

TARGETS="${1:-rust ocaml}"
DUNEJOBS=${DUNEJOBS:-} # required since `set -u`

YELLOW=43
GREEN=42
RED=41
BLACK=40
status () { echo -e "\033[1m[rebuild script] \033[30m\033[$1m$2\033[0m"; }

cd_rootwise () {
    cd $(git rev-parse --show-toplevel)/$1
}

rust () {
    cd_rootwise "cli"
    for i in driver subcommands ../engine/names/extract; do
        CURRENT="rust/$i"
        cargo install --locked --quiet $OFFLINE_FLAG --debug --path $i
    done
}

ocaml () {
    cd_rootwise "engine"
    CURRENT="ocaml"
    dune build $([ -z $DUNEJOBS ] || echo "-j $DUNEJOBS")
    CURRENT="ocaml/install"

    # Small hack for those that are not using [opam] at all: by
    # default install OCaml binaries in `~/.cargo` (which is supposed
    # to be in PATH anyway).
    INSTALL_PREFIX="${OPAM_SWITCH_PREFIX:-${DUNE_INSTALL_PREFIX:-$HOME/.cargo}}"
    dune install --profile dev --prefix $INSTALL_PREFIX

    if ( command -v "which" && command -v "sort" && command -v "wc" ) >/dev/null; then
        case $(which -a hax-engine | sort -u | wc -l) in
            0) status $YELLOW 'Warning: cannot detect `hax-engine` in PATH';;
            1) :;;
            *) status $YELLOW 'Warning: multiple `hax-engine` detected in PATH. Maybe you installed Hax with OPAM (i.e. via `setup.sh`)? Please uninstall it, otherwise you might use a stale engine!';;
        esac
    else
        status $YELLOW 'Warning: cannot run sanity checks because `which`, `sort` or `wc` commands are not available. Please install them.'
    fi
}

on_exit () {
    if [ $? -ne 0 ]; then
        status $RED "ERR: $CURRENT";
    fi
}
trap on_exit                EXIT ERR
trap "status $RED 'SIGINT'" SIGINT

CURRENT="none"
started() { [ -z ${QUIET+x} ] && status $BLACK "$1 build started" || true; }
if [[ "$TARGETS" == *rust* ]]; then
    started rust
    rust
    status $GREEN "rust succeed"
fi
if [[ "$TARGETS" == *ml* ]]; then
    started ocaml
    ocaml
    status $GREEN "ocaml succeed"
fi


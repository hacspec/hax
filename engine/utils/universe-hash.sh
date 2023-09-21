<<<<<<< HEAD
#!/usr/bin/env bash

# this script computes the hash of [hax-export-json-schemas], so that
# whenver this binary change, dune retriggers a generation of
# `types.ml` (see `../lib/dune`).

function fallback() {
    echo "${RANDOM}_$(date +%s)"
}

function hash() {
    if command -v sha256sum &> /dev/null; then
        sha256sum < "$1"
    elif command -v md5sum &> /dev/null; then
        md5sum < "$1"
    elif command -v openssl &> /dev/null; then
        openssl sha256 < "$1"
    else
        fallback
    fi
}

HAX_JSON_SCHEMA_EXPORTER_BINARY=${HAX_JSON_SCHEMA_EXPORTER_BINARY:-hax-export-json-schemas}

if BIN=$(command -v "$HAX_JSON_SCHEMA_EXPORTER_BINARY"); then
    hash "$BIN"
else
    DIAG="looks like it's **NOT** the case!"
    if [[ ":$PATH:" == *":$HOME/.cargo/bin"{,/}":"* ]]; then
        DIAG="this seems to be the case"
    fi
    echo "Error: could not find [$HAX_JSON_SCHEMA_EXPORTER_BINARY] in PATH." >&2
    echo "Please make sure that:" >&2
    echo "  - you ran Hax's `setup.sh` script;" >&2
    echo "  - you have `~/.cargo/bin` in your PATH ($DIAG)." >&2
    exit 1
fi

||||||| parent of 5a59f92 (WIP)
=======
#!/usr/bin/env bash

function hash() {
    if command -v sha256sum &> /dev/null; then
        sha256sum "$1"
    elif command -v md5sum &> /dev/null; then
        md5sum "$1"
    elif command -v openssl &> /dev/null; then
        openssl sha256 "$1"
    else
        # Don't know how to compute a hash
        echo "${RANDOM}_$(date +%s)"
    fi
}

HAX_JSON_SCHEMA_EXPORTER_BINARY=${HAX_JSON_SCHEMA_EXPORTER_BINARY:-hax-export-json-schemas}

hash "$(which "$HAX_JSON_SCHEMA_EXPORTER_BINARY")"
>>>>>>> 5a59f92 (WIP)

#!/usr/bin/env bash

RUST_SOURCE=$(cat "$1")
TEMPDIR=$(mktemp -d)
trap '{ rm -rf -- "$TEMPDIR/"; }' EXIT
DIR="$TEMPDIR/rust-primitives"

mkdir "$DIR" && cd "$DIR"

cargo init --lib

echo "$RUST_SOURCE" > src/lib.rs

cargo hax json --include-extra -o - | jq -r "$(cat - <<JQ_SCRIPT
  .def_ids | . as \$ids
  | map(  (.krate | ((.[0:1] | ascii_upcase) + .[1:]))
        + "__"
        + ( .path | map(
              (.data | if type == "object" then to_entries | first | .value else . end)
            + (.disambiguator | if . == 0 then "" else "_" + (. | tostring) end)
            ) | join("__"))) as \$names
  | "type name = " + (\$names | join(" | \\n"))
  + "\\nmodule Values = struct\\n"
  + ( keys
    | map(. as \$i | "let parsed_" + \$names[\$i] + " = Types.parse_def_id (Yojson.Safe.from_string {hax_gen_def_id|" + (\$ids[\$i] | tojson) + "|hax_gen_def_id})")
    | join("\\n"))
  + "end\\nlet def_id_of: name -> Types.def_id = function "
  + (\$names | map(. + " -> Values.parsed_" + .) | join(" | \\n"))
JQ_SCRIPT
)"

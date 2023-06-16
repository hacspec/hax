RUST_SOURCE=$(cat "$1")
TEMPDIR=$(mktemp -d)
trap '{ rm -rf -- "$TEMPDIR/"; }' EXIT
DIR="$TEMPDIR/hax"

mkdir "$DIR" && cd "$DIR"

cargo init --lib

echo "$RUST_SOURCE" > src/lib.rs

cargo hax json

echo "type name = "
mappings="let def_id_of: name -> Types.def_id = function "
parsed=""

for json in $(
                cat hax_frontend_export.json \
                    | jq 'paths as $p | select(getpath($p) | if type == "object" then has("krate") else false end) | getpath($p) | @base64' -cr \
                    | sort -u
               ); do
    name=$(
        echo "$json" | base64 --decode \
            | jq '(.krate | ((.[0:1] | ascii_upcase) + .[1:])) + "__" + (.path | map((.data | if type == "object" then to_entries | first | .value else . end) + (.disambiguator | if . == 0 then "" else "_" + (. | tostring) end)) | join("__"))' -r
        )
    if [[ "$name" == *"dummy_hax_concrete_ident_wrapper"* ]]; then
        continue
    fi
    echo "$enum | $name"
    parsed=$(
        echo "$parsed"
        echo "let parsed_$name = Types.parse_def_id (Yojson.Safe.from_string {hax_generated_name|$(echo "$json" | base64 --decode)|hax_generated_name})"
          )
    mappings=$(
        echo "$mappings "
        echo "    | $name -> Values.parsed_$name")
done

echo "module Values = struct"
echo "$parsed"
echo "end"
echo "$mappings"


{
    (
        cd ../thir-export
        nix develop --command cargo run --bin thir-export-json-schema -
    ) | node ../ocaml_of_json_schema.js - lib/raw_thir_ast.ml
} && dune fmt

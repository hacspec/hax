This folder contains a rust crate and an OCaml package.
Those two packages test the JS script `../ocaml_of_json_schema.js`.

The rust crate consists of one lib and two binaries.
- `lib.rs`: defines a type `test`.
- binary `ocaml_of_json_schema-schema`: outputs the JSON schema for
  `lib::test`.
- binary `ocaml_of_json_schema-tester`: generate an inhabitant of `test`, send it as JSON on the stdin of `ocaml_of_json_schema_ocaml`, get back an JSON on stdout from `ocaml_of_json_schema_ocaml`, parse it as `test`, compare it with the initial value, panic if it got a bad or different value.

The OCaml part defines the binary `ocaml_of_json_schema_ocaml`. It
inherits the `lib::test` type defined in rust, running
`ocaml_of_json_schema-schema | node ../ocaml_of_json_schema.js`.

The binary `ocaml_of_json_schema_ocaml` parses JSON on stdin,
deserializes it as a value of type `test`, reserializes it as JSON,
and print it on stdout.

# Run the tests
 - `cargo install --path rust`
 - in `./ocaml/`: `dune build --root=. && dune install --root=. --prefix ~/.cargo`
 - in `./rust/`: `cargo run --bin ocaml_of_json_schema-tester`
   Will output `Ok!` if everything is fine.



# Libraries

# Macros and attributes
The hax engine understands only one attribute: `#[_hax::json(PAYLOAD)]`,
where `PAYLOAD` is a JSON serialization of the Rust enum
`hax_lib_macros_types::AttrPayload`.

Note `#[_hax::json(PAYLOAD)]` is a [tool
attribute](https://github.com/rust-lang/rust/issues/66079): an
attribute that is never expanded.

In the engine, the OCaml module `Attr_payloads` offers an API to query
attributes easily. The types in crate `hax_lib_macros_types` and
corresponding serializers/deserializers are automatically generated in
OCaml, thus there is no manual parsing involved.

## User experience
Asking the user to type `#[_hax::json(some_long_json)]` is not very
friendly. Thus, the crate `hax-lib-macros` defines a bunch of [proc
macros](https://doc.rust-lang.org/beta/reference/procedural-macros.html)
that defines nice and simple-to-use macros. Those macro take care of
cooking some `hax_lib_macros_types::AttrPayload` payload(s), then
serialize those payloads to JSON and produce one or more
`#[_hax::json(serialized_payload)]` attributes.


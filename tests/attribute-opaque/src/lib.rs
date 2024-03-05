use hax_lib_macros as hax;

#[hax::opaque_type]
struct OpaqueStruct<const X: usize, T, U> {
    field: [T; X],
    other_field: U,
}

#[hax::opaque_type]
enum OpaqueEnum<const X: usize, T, U> {
    A([T; X]),
    B(U),
}

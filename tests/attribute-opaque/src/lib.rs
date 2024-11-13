#[hax_lib::opaque_type]
struct OpaqueStruct<const X: usize, T, U> {
    field: [T; X],
    other_field: U,
}

#[hax_lib::opaque_type]
enum OpaqueEnum<const X: usize, T, U> {
    A([T; X]),
    B(U),
}

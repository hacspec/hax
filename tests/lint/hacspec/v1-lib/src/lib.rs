use hacspec_lib::*;

bytes!(MyBytes, 8);
array!(State, 16, U32, type_for_indexes: StateIdx);

public_nat_mod!(
    type_name: PublicX25519FieldElement,
    type_of_canvas: PublicFieldCanvas,
    bit_size_of_field: 256,
    modulo_value: "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed"
);

nat_mod!(
    type_name: X25519FieldElement,
    type_of_canvas: FieldCanvas,
    bit_size_of_field: 256,
    modulo_value: "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed"
);

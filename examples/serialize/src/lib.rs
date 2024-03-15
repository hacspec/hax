use hax_lib_macros::{ensures, requires};

#[derive(PartialEq, Eq, Debug, Clone)]
struct Value {
    tag: u8,
    bytes: Vec<u8>,
}

// #[requires(bytes.len() >= 2)]
fn deserialize(bytes: &[u8]) -> Value {
    let tag = bytes[0];
    let bytes = bytes[1..].to_vec();

    Value { tag, bytes }
}

const USIZE_MAX_32: usize = 4294967295;

// #[requires(value.bytes.len() > 0 && value.bytes.len() < USIZE_MAX_32 - 1)]
// #[ensures(|result| result.len() >= 2)]
fn serialize(value: &Value) -> Vec<u8> {
    let mut out = Vec::new();

    out.extend_from_slice(&[value.tag]);
    out.extend_from_slice(&value.bytes);

    out
}

// #[requires(value.bytes.len() > 0 && value.bytes.len() < USIZE_MAX_32 - 1)]
// #[ensures(|result| result == value)]
fn inverse(value: Value) -> Value {
    let serialized = serialize(&value);
    deserialize(&serialized)
}

#[test]
fn inverse_test() {
    let v = Value {
        tag: 5,
        bytes: vec![1, 2, 3],
    };

    let serialized = serialize(&v);
    let value = deserialize(&serialized);
    assert_eq!(v, value);
}

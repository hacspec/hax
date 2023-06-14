#![allow(dead_code)]

pub fn panic_with_msg() {
    panic!("with msg")
}

#[derive(PartialEq, Eq)]
struct Foo {
    field: u8,
}

const CONSTANT: Foo = Foo { field: 3 };

pub fn patterns() {
    match 1u8 {
        2 => (),
        _ => (),
    };
    match ("hello", (123, ["a", "b"])) {
        ("hello", (123, _todo)) => (),
        _ => (),
    };
    match (Foo { field: 4 }) {
        CONSTANT => (), // Note [CONSTANT] is not a free variable here, we're really matching against the *value* of CONSTANT
        _ => (),
    };
}

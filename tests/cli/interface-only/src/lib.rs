#![allow(dead_code)]

/// This item contains unsafe blocks and raw references, two features
/// not supported by hax. Thanks to the `-i` flag and the `+:`
/// modifier, `f` is still extractable as an interface.
fn f(x: u8) {
    let y = x as *const i8;

    unsafe {
        println!("{}", *y);
    }
}

/// This struct contains a field which uses raw pointers, which are
/// not supported by hax. This item cannot be extracted at all: we
/// need to exclude it with `-i '-*::Foo'`.
struct Foo {
    unsupported_field: *const u8,
}

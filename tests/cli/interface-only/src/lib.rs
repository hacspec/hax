#![allow(dead_code)]

use hax_lib as hax;

/// This item contains unsafe blocks and raw references, two features
/// not supported by hax. Thanks to the `-i` flag and the `+:`
/// modifier, `f` is still extractable as an interface.
///
/// Expressions within type are still extracted, as well as pre- and
/// post-conditions.
#[hax::requires(x < 254)]
#[hax::ensures(|r| r[0] > x)]
fn f(x: u8) -> [u8; 4] {
    let y = x as *const i8;

    unsafe {
        println!("{}", *y);
    }

    [x + 1, x, x, x]
}

/// This struct contains a field which uses raw pointers, which are
/// not supported by hax. This item cannot be extracted at all: we
/// need to exclude it with `-i '-*::Foo'`.
struct Foo {
    unsupported_field: *const u8,
}

struct Bar;

/// Non-inherent implementations are extracted, their bodies are not
/// dropped. This might be a bit surprising: see
/// https://github.com/hacspec/hax/issues/616.
impl From<()> for Bar {
    fn from((): ()) -> Self {
        Bar
    }
}

/// If you need to drop the body of a method, please hoist it:
impl From<u8> for Bar {
    fn from(x: u8) -> Self {
        fn from(_: u8) -> Bar {
            Bar
        }
        from(x)
    }
}

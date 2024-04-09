#![allow(dead_code)]

pub fn panic_with_msg() {
    panic!("with msg")
}

#[derive(PartialEq, Eq)]
struct Foo {
    field: u8,
}

const CONSTANT: Foo = Foo { field: 3 };

fn numeric() {
    let _: usize = 123;
    let _: isize = -42;
    let _: isize = 42;
    let _: i32 = -42;
    let _: u128 = 22222222222222222222;
}

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

fn casts(x8: u8, x16: u16, x32: u32, x64: u64, xs: usize) {
    let _: u64 = x8 as u64 + x16 as u64 + x32 as u64 + x64 as u64 + xs as u64;
    let _: u32 = x8 as u32 + x16 as u32 + x32 as u32 + x64 as u32 + xs as u32;
    let _: u16 = x8 as u16 + x16 as u16 + x32 as u16 + x64 as u16 + xs as u16;
    let _: u8 = x8 as u8 + x16 as u8 + x32 as u8 + x64 as u8 + xs as u8;
    let _: i64 = x8 as i64 + x16 as i64 + x32 as i64 + x64 as i64 + xs as i64;
    let _: i32 = x8 as i32 + x16 as i32 + x32 as i32 + x64 as i32 + xs as i32;
    let _: i16 = x8 as i16 + x16 as i16 + x32 as i16 + x64 as i16 + xs as i16;
    let _: i8 = x8 as i8 + x16 as i8 + x32 as i8 + x64 as i8 + xs as i8;
}

pub fn empty_array() {
    let _: &[u8] = &[];
}

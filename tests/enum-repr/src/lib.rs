#![allow(dead_code)]

#[repr(u16)]
enum Foo {
    A = 1,
    B = 5,
    C = 9,
}

fn f() -> u16 {
    const CONST: u16 = Foo::A as u16;
    let _x = Foo::B as u16;
    Foo::C as u16
}

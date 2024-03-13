#![allow(dead_code)]

#[repr(u16)]
enum Foo {
    A = 1,
    B = 5,
    C(),
    D {},
}

fn f() -> u16 {
    const CONST: u16 = Foo::A as u16;
    let _x = Foo::B as u16;
    Foo::C as u16
}

fn get_repr(x: Foo) -> u16 {
    x as u16
}

fn get_casted_repr(x: Foo) -> u64 {
    x as u64
}

#![allow(dead_code)]

fn g() -> Bar {
    Bar(f(32))
}
fn f(_: u32) -> Foo {
    Foo::A
}

struct Bar(Foo);
enum Foo {
    A,
    B,
}

#![allow(dead_code)]

enum Foo {
    A,
    B { x: usize },
}
enum Foo2 {
    A,
    B { x: usize },
}
struct B;

struct C {
    x: usize,
}

struct X {}

fn mk_c() -> C {
    let _ = Foo::B { x: 3 };
    let _ = X {};
    C { x: 3 }
}

impl Foo {
    fn f(self) -> Foo {
        Foo::A
    }
}
impl B {
    fn f(self) -> B {
        B
    }
}

struct Foobar {
    a: Foo,
}

fn f(x: Foobar) -> usize {
    fn g() {
        impl B {
            fn g(self) -> usize {
                enum Foo {
                    A,
                    B { x: usize },
                }
                0usize
            }
        }
        impl Foo {
            fn g(self) -> usize {
                mod hello {
                    fn h() {}
                }
                1usize
            }
        }
    }
    x.a.g()
}

fn reserved_names(val: u8, noeq: u8, of: u8) -> u8 {
    val + noeq + of
}

struct Arity1<T>(T);

trait T1 {}
impl T1 for Foo {}
impl T1 for (Foo, u8) {}

trait T2_for_a {}
impl T2_for_a for Arity1<(Foo, u8)> {}
trait T3_e_for_a {}
impl T3_e_for_a for Foo {}

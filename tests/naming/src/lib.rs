#![allow(dead_code)]
#![allow(non_camel_case_types)]

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

struct StructA {
    a: usize,
}
struct StructB {
    a: usize,
    b: usize,
}
struct StructC {
    a: usize,
}
struct StructD {
    a: usize,
    b: usize,
}
fn construct_structs(a: usize, b: usize) {
    let _ = StructA { a };
    let _ = StructB { a, b };
    let _ = StructC { a };
    let _ = StructD { a, b };
}

const INHERENT_CONSTANT: usize = 3;
trait FooTrait {
    const ASSOCIATED_CONSTANT: usize;
}

fn constants<T: FooTrait>() -> usize {
    <T as FooTrait>::ASSOCIATED_CONSTANT + INHERENT_CONSTANT
}

mod ambiguous_names {
    fn debug(label: &str, value: u32) {
        println!("[{}] a={}", label, value)
    }

    macro_rules! hello {
        ($label:expr, $value:expr, $($e:tt)*) => {
            let a = $value;
            $($e)*
            debug($label, a)
        };
    }

    fn f() {
        hello!("1", 104,
               hello!("2", 205,
                      hello!("3", 306, let a = 123;);
               );
        );
        debug("last", a)
    }
}

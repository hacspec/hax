#![allow(dead_code)]

fn no_dependency_1() {}

fn g() -> Bar {
    Bar(f(32))
}

fn no_dependency_2() {}

fn f(_: u32) -> Foo {
    Foo::A
}

struct Bar(Foo);
enum Foo {
    A,
    B,
}

mod mut_rec {
    fn f() {
        g()
    }

    fn f_2() {
        f()
    }

    fn g() {
        f()
    }
}

mod independent_cycles {
    fn a() {
        c()
    }
    fn b() {
        d()
    }
    fn c() {
        a()
    }
    fn d() {
        b()
    }
}

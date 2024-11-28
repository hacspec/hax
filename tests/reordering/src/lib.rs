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

/// From issue https://github.com/hacspec/hax/issues/771
mod no_dependency {
    fn u01() {}
    fn r02() {}
    fn b03() {}
    fn f04() {}
    fn h05() {}
    fn i06() {}
    fn c07() {}
    fn k08() {}
    fn d09() {}
    fn e10() {}
    fn g11() {}
    fn j12() {}
    fn o13() {}
    fn a14() {}
    fn q15() {}
    fn m16() {}
    fn l17() {}
    fn n18() {}
    fn v19() {}
    fn s20() {}
    fn p21() {}
    fn t22() {}
}

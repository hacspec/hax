#![allow(dead_code)]

pub trait Foo {
    const N: usize;
    fn assoc_f() -> ();
    fn method_f(&self) -> ();
}

impl Foo for () {
    const N: usize = 32;
    fn assoc_f() {
        ()
    }
    fn method_f(&self) {
        Self::assoc_f()
    }
}

fn f<T: Foo>(x: T) {
    T::assoc_f();
    x.method_f()
}

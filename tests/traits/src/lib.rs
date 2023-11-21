#![allow(dead_code)]

pub trait SuperTrait: Clone {
    fn function_of_super_trait(self) -> u32;
}

pub trait Foo {
    type AssocType: SuperTrait;
    const N: usize;
    fn assoc_f() -> ();
    fn method_f(&self) -> ();
}

impl SuperTrait for i32 {
    fn function_of_super_trait(self) -> u32 {
        self.abs() as u32
    }
}

impl Foo for () {
    type AssocType = i32;
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

fn g<T: Foo>(x: T::AssocType) -> u32 {
    x.function_of_super_trait()
}

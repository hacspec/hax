#![allow(dead_code)]

pub trait SuperTrait: Clone {
    fn function_of_super_trait(self) -> u32;
}

pub trait Foo {
    type AssocType: SuperTrait;
    const N: usize;
    fn assoc_f() -> ();
    fn method_f(&self) -> ();
    fn assoc_type(_: Self::AssocType) -> ()
    where
        Self::AssocType: Copy;
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
    fn assoc_type(_: Self::AssocType) -> () {}
}

fn f<T: Foo>(x: T) {
    T::assoc_f();
    x.method_f()
}

fn g<T: Foo>(x: T::AssocType) -> u32 {
    x.function_of_super_trait()
}

struct Struct;

trait Bar<'a> {
    fn bar(self);
}

impl<'a> Struct {
    fn method<T: Bar<'a>>(x: T) {
        x.bar()
    }
}

pub fn closure_impl_expr<I: Iterator<Item = ()>>(it: I) -> Vec<()> {
    it.map(|x| x).collect()
}

pub fn closure_impl_expr_fngen<I: Iterator<Item = ()>, F: FnMut(()) -> ()>(it: I, f: F) -> Vec<()> {
    it.map(f).collect()
}

// From issue #523
pub trait Lang: Sized {
    type Var;
    fn s(self, _: i32) -> (Self, Self::Var);
}

pub enum Error {
    Fail,
}

// From issue #474
impl Error {
    pub fn for_application_callback() -> impl FnOnce() -> Self {
        || Self::Fail
    }
}

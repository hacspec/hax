#![allow(dead_code)]
pub struct Foo {
    pub a : Option<usize>,
    pub b : usize,
}

pub fn bar(x : Option<Foo>) -> usize {
    match x {
        Some(Foo {a: None, b}) => b,
        Some(Foo {a: Some(a), b}) => a + b,
        None => 0,
    }
}

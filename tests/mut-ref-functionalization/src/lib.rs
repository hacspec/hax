#![allow(dead_code)]

struct S {
    b: [u8; 5],
}

impl S {
    fn update(&mut self, x: u8) {
        self.b[0] = x;
    }
}

fn index_mutation(x: core::ops::Range<usize>, a: &'static [u8]) {
    let mut v = vec![1];
    v[x].copy_from_slice(a);
    v[1] = 3;
}

fn index_mutation_unsize(mut x: [u8; 12]) -> u8 {
    x[4..5].copy_from_slice(&[1, 2]);
    42
}

fn build_vec() -> Vec<u8> {
    vec![1, 2, 3]
}

fn test_append() -> Vec<u8> {
    let mut vec1 = Vec::new();
    let mut vec2 = vec![1u8, 2, 3];
    vec1.append(&mut vec2);
    vec1.append(&mut build_vec());
    vec1
}

fn f() -> Vec<u8> {
    let mut vec = Vec::new();
    vec.push(1);
    vec.push(2);
    vec.swap(0, 1);

    // `vec.swap(0, 1)` is desugared into:
    use std::ops::DerefMut;
    (&mut *(vec.deref_mut())).swap(0, 1);

    vec
}

struct Foo {
    field: Vec<u8>,
}
struct Pair<T> {
    a: T,
    b: Foo,
}

fn g(x: Pair<Vec<u8>>) -> Vec<u8> {
    let mut x = x;
    for i in 1..10 {
        x.a.push(i);
    }
    x.a.swap(0, 1);
    x.b.field.swap(0, 1);
    x.a
}

struct Bar {
    a: u8,
    b: u8,
}

fn h(x: &mut u8) {
    *x += 10;
}

fn i(bar: &mut Bar) -> u8 {
    (*bar).b += bar.a;
    h(&mut bar.a);
    bar.a + bar.b
}

fn j(x: &mut Bar) -> u8 {
    i(x)
}

trait FooTrait {
    fn z(&mut self);
}
impl FooTrait for Foo {
    fn z(&mut self) {}
}

fn array(x: &mut [u8; 10]) {
    x[1] = x[2];
}

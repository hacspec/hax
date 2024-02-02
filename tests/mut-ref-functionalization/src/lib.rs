#![allow(dead_code)]

struct S {
    b: [u8; 5],
}

fn foo(mut lhs: S, rhs: &S) -> S {
    for i in 0..1 {
        lhs.b[i] += rhs.b[i];
    }

    lhs
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

fn h(x: &mut u8) {
    *x += 10;
}

struct Bar {
    a: u8,
    b: u8,
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

// XXX: (RefMut) At this position, Hax was expecting an expression of the shape
//      `&mut _`. Hax forbids `f(x)` (where `f` expects a mutable reference as
//      input) when `x` is not a place expression[1] or when it is a dereference
//      expression.
//
// NOTE: This goes through when `a` is an array.
fn xor(mut a: Vec<u8>, b: [u8; 4]) -> Vec<u8> {
    for i in 0..4 {
        a[i] ^= b[i]
    }
    a
}

enum Value {
    A,
    B(Vec<u8>),
}

// XXX: (RefMut) The mutation of this &mut is not allowed here.
//
// Not sure if this should be allowed or not.
fn set(mut val: Value, b: Vec<u8>) -> Value {
    match &mut val {
        Value::A => (),
        Value::B(v) => *v = b,
    }
    val
}

use std::collections::HashMap;
// XXX: (reject_ArbitraryLhs) ExplicitRejection { reason: "a node of kind [Arbitrary_lhs] have been found in the AST" }
fn update(mut val: Option<HashMap<u8, u8>>, new: (u8, u8)) -> Option<HashMap<u8, u8>> {
    let _ = val.as_mut().unwrap().insert(new.0, new.1);
    val
}

struct OMapValue(HashMap<u8, u8>);
struct OMap {
    val: Option<OMapValue>,
}
// XXX: (RefMut) At this position, Hax was expecting an expression of the shape `&mut _`.
fn update2(mut val: OMap, new: (u8, u8)) -> OMap {
    let _ = val.val.as_mut().unwrap().0.insert(new.0, new.1);
    val
}

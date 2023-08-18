#![allow(dead_code)]

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

#![allow(dead_code)]
#![allow(non_camel_case_types)]

/// Entrypoint
fn main() {
    main_a(Foo);
    main_b();
    main_c();
}

/// Direct dependencies
fn main_a<T: Trait>(x: T) {
    main_a_a();
    main_a_b();
    main_a_c();
}
fn main_b() {
    main_b_a();
    main_b_b();
    main_b_c();
}
fn main_c() {
    main_c_a();
    main_c_b();
    main_c_c();
}
struct Foo;

trait Trait {}
impl Trait for Foo {}

/// Indirect dependencies
fn main_a_a() {}
fn main_b_a() {}
fn main_c_a() {}

fn main_a_b() {}
fn main_b_b() {}
fn main_c_b() {}

fn main_a_c() {}
fn main_b_c() {}
fn main_c_c() {}

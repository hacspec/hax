// #![feature(never_type)]
#![allow(dead_code, unused)]

mod hash;
use hash::*;
use hex::*;
use serde::{Deserialize, Serialize};
use serde_json::to_string as to_json_string;

fn serde_json_print() {
    let s = to_json_string(&[0, 1, 2]).unwrap();
    println!("I'm a function {}", encode(s));
}

trait Features {
    type Mutability;
    type EarlyExit;
}

enum Expr<T: Features> {
    Loop {
        body: Box<Expr<T>>,
    },
    Break {
        body: Box<Expr<T>>,
        witness: T::EarlyExit,
    },
    Assign {
        var: String,
        value: Box<Expr<T>>,
        witness: T::Mutability,
    },
}

macro_rules! helper_macro {
    ($x:expr) => {
        $x + 10
    };
}

macro_rules! library_foo {
    (make $x:ident 32 unsigned) => {
        $x as u32
    };
}

#[derive(Clone)]
struct FooStruct {
    field_a: u8,
    field_b: u16,
    field_c: u16,
}

fn some_option() -> Option<u8> {
    Some(5)
}

// #[derive(Clone)]
// enum Bar {
//     BarA(u8, u16),
//     BarB {
//         bar_b_field_1: u32,
//         bar_b_field_2: u64,
//     },
// }

// fn f<T: Into<u32>>(tuple @ (a, b): (u8, u16), x: u8, t: T, foo: FooStruct, bar: Bar) -> u32 {
//     match bar {
//         Bar::BarA(0, 0) => library_foo!(make x 32 unsigned),
//         Bar::BarA(_, b) => (b as u32) + (foo.field_a as u32),
//         Bar::BarB { bar_b_field_1, .. } => bar_b_field_1,
//         _ => helper_macro!(t.into()),
//     }
// }
// mod hash;

pub fn my_fun() {
    let x = 5;
    let _y = unsafe { 8 };
    loop {
        break;
    }
    while x > 4 {
        break;
    }
}

pub unsafe fn unsafe_fun() {
    let _x = 7;
}

pub async fn async_fun() {
    let mut x = 8;
    let y = &mut x;
}

pub trait MyTraitWithAssoc {
    type Error;
    fn run(&self);
}

pub trait MyTrait {
    fn run(&self);
}

pub fn trait_obj_fun(trait_obj: &dyn MyTrait) {
    trait_obj.run();
}

pub fn trait_obj_fun2(trait_obj: &impl MyTrait) {
    trait_obj.run();
}

pub fn trait_obj_fun3(trait_obj: impl MyTrait) {
    trait_obj.run();
}

pub fn explicit_lifetime<'a>(x: &'a u8) -> u8 {
    *x
}

fn update<F1, F2>(f1: F1, mut f2: F2) -> u8
where
    F1: Fn(u8) -> u8,
    F2: FnMut(u8) -> u8,
{
    let x = 5;
    f1(1) + f2(x)
}

pub union SomeUnion {
    a: u8,
}

#[derive(Copy, Clone, Serialize, Deserialize, Hash)]
struct DummyStruct {
    dummy: u8,
}

enum Hello {
    A(u8, u8),
    B { x: u8, y: u8 },
}

trait Foo: Copy + Clone {
    fn bar(self) -> u8 {
        123
    }
}

impl DummyStruct {
    fn member_fun(&self) {
        let s = to_json_string(self).unwrap();
        println!("I'm a member function {}", encode(s));
    }

    fn update(&mut self) {
        println!("update self");
    }
}

impl Foo for DummyStruct {
    fn bar(self) -> u8 {
        5
    }
}

trait TraitWithFun {
    fn update<F>(&self, f: F) -> u8
    where
        F: FnMut(u8) -> u8;
}

impl TraitWithFun for DummyStruct {
    fn update<F>(&self, mut f: F) -> u8
    where
        F: FnMut(u8) -> u8,
    {
        f(6)
    }
}

#[derive(Debug)]
struct Hi {
    field1: u8,
    field2: u8,
    field3: u8,
    field4: u8,
}

fn f3<A>(x: u8, y: A) -> u8
where
    A: Foo,
{
    5
}

fn f2<A: Foo>(x: u8, y: A) -> u8 {
    let foo = 1u16 + 4;
    let a = Hello::A(2, 5);
    let b = Hello::B { y: 99, x: 123 };
    let hi = Hi {
        field1: 10,
        field2: 20,
        field3: 30,
        field4: 40,
    };
    if true {
        3 + x
    } else {
        match 1 {
            0 => 12,
            1 => match b {
                Hello::A(x, y) => 1,
                Hello::B { y, x } => 2,
            },
            _ => match hi {
                Hi {
                    field1,
                    field2,
                    field3,
                    field4,
                } => field3,
            },
        }
    }
}

fn g() -> u8 {
    f2(3, DummyStruct { dummy: 9 })
}

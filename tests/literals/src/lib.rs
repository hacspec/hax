#![allow(dead_code)]

trait TrA {
    type TypeA: TrB;
    fn tr_a(&self) {}
}

mod foo {
    pub trait TrB {
        const CONST_B: usize;
        type TypeB: Clone;
        fn tr_b(&self) {}
    }
    pub struct StructC {
        pub x_field: u8,
    }

    impl StructC {
        pub fn say_hi(&self) {}
    }
}
use foo::*;

fn x<A: TrA, B: TrB>(a: A, aa: A::TypeA, b: B, bb: B::TypeB, z: <A::TypeA as TrB>::TypeB) -> usize {
    a.tr_a();
    aa.tr_b();
    b.tr_b();
    let _ = bb.clone();
    let _ = z.clone();
    <A::TypeA as TrB>::CONST_B
}

fn y(x: StructC) -> u8 {
    x.say_hi();
    fn yy() {
        fn yyy() {
            struct Yyyy;
            let _ = Yyyy;
        }
    }
    x.x_field
}

trait TrD<T: Clone> {
    fn f<U: Copy>(t: T, u: U) {}
}

// trait Foo {
//     type Bar;
// }

// fn hello<T: Foo>(_x: T::Bar) {}

// impl Foo {
//     fn foo(&self) {}
// }

// impl Clone for Foo {
//     fn clone(&self) -> Self {
//         let _ = Some(3u8).clone();
//         Foo
//     }
// }

// fn f<T: Hello>(x: T) -> usize {
//     T::N
// }

// trait A: Clone {
//     fn f(&self) -> Self;
// }

// impl<T: A> A for (T,) {
//     fn f(&self) -> Self {
//         (self.0.clone(),)
//     }
// }

// trait Foo: Bar<Self::U> {
//     type U;
// }
// trait Bar<T> {}

// impl Bar<u16> for u8 {}

// impl Foo for u8 {
//     type U = u16;
// }

// impl<A, B: Bar<A>> Bar<(A,)> for (B,) {}

// impl<A: Foo> Foo for (A,) {
//     type U = (A::U,);
// }

// impl Foo for u8 {
//     type U = u64;
// }

// trait A {}
// trait Foo {
//     type T;
// }

// fn hello<G: Foo>(_blibx: G::T) {}

// fn f() {
//     ()
// }

// pub fn panic_with_msg() {
//     panic!("with msg")
// }

// #[derive(PartialEq, Eq)]
// struct Foo {
//     field: u8,
// }

// const CONSTANT: Foo = Foo { field: 3 };

// pub fn patterns() {
//     match 1u8 {
//         2 => (),
//         _ => (),
//     };
//     match ("hello", (123, ["a", "b"])) {
//         ("hello", (123, _todo)) => (),
//         _ => (),
//     };
//     match (Foo { field: 4 }) {
//         CONSTANT => (), // Note [CONSTANT] is not a free variable here, we're really matching against the *value* of CONSTANT
//         _ => (),
//     };
// }

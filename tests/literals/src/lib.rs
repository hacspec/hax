#![allow(dead_code)]

trait A: Clone {
    fn f(&self) -> Self;
}

impl<T: A> A for (T,) {
    fn f(&self) -> Self {
        (self.0.clone(),)
    }
}

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

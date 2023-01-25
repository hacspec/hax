// #![feature(never_type)]

// trait Features {
//     type Mutability;
//     type EarlyExit;
// }

// enum Expr<T: Features> {
//     Loop {
//         body: Box<Expr<T>>,
//     },
//     Break {
//         body: Box<Expr<T>>,
//         witness: T::EarlyExit,
//     },
//     Assign {
//         var: String,
//         value: Box<Expr<T>>,
//         witness: T::Mutability,
//     },
// }

// macro_rules! helper_macro {
//     ($x:expr) => {
//         $x + 10
//     };
// }

// macro_rules! library_foo {
//     (make $x:ident 32 unsigned) => {
//         $x as u32
//     };
// }

// #[derive(Clone)]
// struct Foo {
//     field_a: u8,
//     field_b: u16,
//     field_c: u16,
// }

// #[derive(Clone)]
// enum Bar {
//     BarA(u8, u16),
//     BarB {
//         bar_b_field_1: u32,
//         bar_b_field_2: u64,
//     },
// }

// fn f<T: Into<u32>>(tuple @ (a, b): (u8, u16), x: u8, t: T, foo: Foo, bar: Bar) -> u32 {
//     match bar {
//         Bar::BarA(0, 0) => library_foo!(make x 32 unsigned),
//         Bar::BarA(_, b) => (b as u32) + (foo.field_a as u32),
//         Bar::BarB { bar_b_field_1, .. } => bar_b_field_1,
//         _ => helper_macro!(t.into()),
//     }
// }

fn hello(x: &mut u8) {}

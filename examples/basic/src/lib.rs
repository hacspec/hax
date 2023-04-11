#![feature(structural_match)]
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
// mod hash;

// fn test() -> u8 {
//     let mut acc = 0;
//     for i in 1..10 {
//         acc = acc + i;
//     };
//     acc + 1
// }


// #![feature(register_tool)]
// #![register_tool(my_tool)]

// // const X: usize = 0;
// type X = (u8, u8);
// fn f(#[my_tool::hello(3 + 34)] a: X) {}
// fn f(x: u8, y: u8) -> u8 {
//     x + (y - 2) * 3
// }

// #[derive(Copy, Clone)]
// struct DummyStruct {
//     dummy: u8
// }

// enum Hello {
//     A(u8, u8),
//     B { x: u8, y: u8 },
// }

// trait Foo: Copy + Clone {
//     fn bar(self) -> u8 {
//         123
//     }
// }

// impl Foo for DummyStruct {}

// struct Hi {
//     field1: u8,
//     field2: u8,
//     field3: u8,
//     field4: u8,
// }

// fn f<A: Foo>(x: u8, y: A) -> u8
// {
//     let foo = 1u16 + 4;
//     let a = Hello::A(2, 5);
//     let b = Hello::B { y: 99, x: 123 };
//     let hi = Hi {
//         field1: 10,
//         field2: 20,
//         field3: 30,
//         field4: 40,
//     };
//     if true {
//         3 + x
//     } else {
//         match 1 {
//             0 => 12,
//             1 => match b {
//                 Hello::A(x, y) => 1,
//                 Hello::B { y, x } => 2,
//             },
//             _ => match hi {
//                 Hi {
//                     field1,
//                     field2,
//                     field3,
//                     field4,
//                 } => field3,
//             },
//         }
//     }
// }

// fn g() -> u8 {
//     f(3, DummyStruct{dummy: 9})
// }

pub trait Temp<A> {
    fn my (xx : u64, xy : u32, xw : A, xz : u16) -> Self;
    fn x (yy : u64) -> Self;
    fn y (zz : u64) -> Self;
    fn z (ww : u64) -> Self;
    // const t : u64;
}

impl Temp<u8> for u64 {
    fn my (xx : u64, xy : u32, xw : u8, xz : u16) -> u64 {
        xx
    }

    fn x (yy : u64) -> u64 {
        yy
    }
    fn y (zz : u64) -> u64 {
        zz
    }

    fn z (ww : u64) -> u64 {
        ww
    }
    // const t : u64 = 16;
}

// struct MyData {
//     temp : u64
// }

// impl Default for MyData {
//     fn default() -> Self {
//         MyData { temp: 32 }
//     }
// }

#![allow(dead_code)]
#![feature(if_let_guard)]

struct Foo {
    a : Option<usize>,
    b : usize,
}

pub fn test (x : Foo, y : Foo) -> bool {
    match (x, y) {
        (Foo {a: None, b:_}, Foo {a: None, b:_}) =>
            true,
        (Foo {a: Some(c), b:_}, Foo {a: Some(d), b:_}) =>
            c == d,
        _ => false,
    }
}

pub fn test2 (x : Foo, y : Foo) -> bool {
    match x {
        Foo {a: None, b:_} =>
            match y {
                Foo {a: None, b:_} =>
                    true,
                _ => false,
            }
        Foo {a: Some(c), b:_} =>
            match y {
                Foo {a: Some(d), b:_} =>
                    c == d,
                _ => false,
            }
        _ => false,
    }
}

// pub fn foo(x : Option<Foo>) -> usize {
//     match x {
//         Some(Foo {a: None, b}) => b,
//         None => 0,
//         Some(Foo {a: Some(a), b}) => a + b,
//     }
// }

// pub fn bar(x : Option<Foo>) -> usize {
//     match x {
//         Some(f) if if let (None, b) = (f.a, f.b) { true } else { false } => {
//             let None = f.a;
//             let b = f.b;
//             b
//         }
//         None => 0,
//         Some(f) if if let (Some(a), b) = (f.a, f.b) { true } else { false } => {
//             let Some(a) = f.a;
//             let b = f.b;
//             a + b
//         },
//     }
// }

// pub fn bar(x : Option<Sum>) -> usize {
//     if let Some(y) = x {
//         if let Left = y {
//             return 1;
//         }
//     };

//     if let None = x {
//         return 0;
//     };

//     if let Some(y) = x {
//         if let Right = y {
//             return 2;
//         }
//     };

//     1000 // default // TODO
// }

// if let x = Some(Left) {
//     continue
// }
// if let x = None {
//     continue
// }

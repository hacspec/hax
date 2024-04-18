// enum Path::Foo {
//   Path::Foo::Variant1 {f1: T1, ..., fN: TN},
// }

struct Foo {
    a: u8,
    b: bool,
    c: u16,
}

// Record updates are supported
fn Foo() {
    let foo = Foo {
        a: 16,
        b: false,
        c: 9,
    };
    let bar = Foo { c: 14, ..foo };
}

// Record matching is supported
fn Bar(foo: Foo) {
    match foo {
        Foo { c, .. } => 1,
    };
}

// Conditional Record matching is supported
fn Baz(foo: Foo) {
    match foo {
        Foo { a, .. } if a > 10 => 1,
        Foo { b, .. } if b => 2,
        _ => 3,
    };
}

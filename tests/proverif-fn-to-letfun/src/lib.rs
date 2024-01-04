struct A {
    x: usize,
    y: u8,
}
struct B {
    b: bool,
}

fn some_function() -> bool {
    true
}

fn some_other_function(b: bool) -> u8 {
    5
}

fn longer_function(x: &str) -> A {
    let b = some_function();
    let d = some_other_function(b);

    A { x: 12usize, y: 9u8 }
}

fn another_longer_function() -> B {
    let b = some_function();
    let d = some_other_function(b);

    B { b: false }
}

fn void_function() {
    let b = some_function();
    let d = some_other_function(b);
}

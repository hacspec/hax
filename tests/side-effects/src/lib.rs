#![allow(dead_code)]

/// Helper function
fn add3(x: u32, y: u32, z: u32) -> u32 {
    x.wrapping_add(y).wrapping_add(z)
}

/// Exercise local mutation with control flow and loops
fn local_mutation(mut x: u32) -> u32 {
    let mut y = 0;
    if {
        x = x.wrapping_add(1);
        x > 3
    } {
        x = x.wrapping_sub(3);
        let mut y = x / 2;
        for i in {
            y = y.wrapping_add(2);
            0
        }..10
        {
            y = x.wrapping_add(i);
        }
        x.wrapping_add(y)
    } else {
        x = match x {
            12 => {
                y = x.wrapping_add(y);
                3
            }
            13 => add3(
                x,
                {
                    x = x.wrapping_add(1);
                    123u32.wrapping_add(x)
                },
                x,
            ),
            _ => 0,
        };
        x.wrapping_add(y)
    }
}

/// Exercise early returns with control flow and loops
fn early_returns(mut x: u32) -> u32 {
    return (123u32.wrapping_add(
        if {
            if x > 3 {
                return 0;
            };
            x > 30
        } {
            match true {
                true => return 34,
                _ => 3,
            }
        } else {
            x = x + 9;
            x + 1
        },
    ))
    .wrapping_add(x);
}

fn simplifiable_return(c1: bool, c2: bool, c3: bool) -> i32 {
    let mut x = 0;
    if c1 {
        if c2 {
            x += 10;
            if c3 {
                return 1;
            }
        }
        x += 1;
    }
    x
}

fn simplifiable_question_mark(c: bool, x: Option<i32>) -> Option<i32> {
    let a = if c { x? + 10 } else { 0 };
    let b = 20;
    Some(a + b)
}

/// Question mark without error coercion
fn direct_result_question_mark(y: Result<(), u32>) -> Result<i8, u32> {
    y?;
    Ok(0)
}

/// Question mark with an error coercion
fn direct_result_question_mark_coercion(y: Result<i8, u16>) -> Result<i8, u32> {
    Ok(y?)
}

/// Test question mark on `Option`s with some control flow
fn options(x: Option<u8>, y: Option<u8>, z: Option<u64>) -> Option<u8> {
    let v = match (if x? > 10 {
        Some(x?.wrapping_add(3))
    } else {
        Some(x?.wrapping_add(y?))
    })? {
        3 => None?,
        4 => 4 + (if z? > 4 { 0 } else { 3 }),
        _ => 12u8,
    };
    Some(v.wrapping_add(x?).wrapping_add(y?))
}

/// Test question mark on `Result`s with local mutation
fn question_mark(mut x: u32) -> Result<u32, u32> {
    if x > 40u32 {
        let mut y = 0;
        x = x.wrapping_add(3);
        y = x.wrapping_add(y);
        if {
            x = x.wrapping_add(y);
            x > 90u32
        } {
            Err(12u8)?
        }
    };
    Ok(3u32.wrapping_add(x))
}

struct A;
struct B;

/// Combine `?` and early return
fn monad_lifting(x: u8) -> Result<A, B> {
    if x > 123 {
        return Ok(Err(B)?);
    } else {
        Ok(A)
    }
}

struct Bar {
    a: bool,
    b: ([(bool, bool); 6], bool),
}
struct Foo {
    x: bool,
    y: (bool, Vec<Bar>),
    z: [Bar; 6],
    bar: Bar,
}

/// Test assignation on non-trivial places
fn assign_non_trivial_lhs(mut foo: Foo) -> Foo {
    foo.x = true;
    foo.bar.a = true;
    foo.bar.b.0[3].1 = true;
    foo.z[3].a = true;
    foo.y.1[3].b.0[5].0 = true;
    foo
}

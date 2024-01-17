#![allow(dead_code)]
fn add3(x: u32, y: u32, z: u32) -> u32 {
    x.wrapping_add(y).wrapping_add(z)
}

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

fn direct_result_1(y: Result<i8, u32>) -> Result<i8, u32> {
    Ok(y?)
}
fn direct_result_2(y: Result<(), u32>) -> Result<i8, u32> {
    y?;
    Ok(1)
}

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

fn monad_lifting() -> Result<A, B> {
    return Ok(Err(B)?);
}

fn into_err(x: u8) -> Result<u8, u64> {
    if x > 200 {
        Err(x)?
    }
    Ok(x.wrapping_add(54))
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
fn assign_non_trivial_lhs(mut foo: Foo) -> Foo {
    foo.x = true;
    foo.bar.a = true;
    foo.bar.b.0[3].1 = true;
    foo.z[3].a = true;
    foo.y.1[3].b.0[5].0 = true;
    foo
}

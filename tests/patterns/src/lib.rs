#![allow(dead_code)]

struct Other<'a>(&'a i32);

enum Test<'a> {
    C1(Other<'a>),
}

impl<'a> Test<'a> {
    fn test(&self) -> i32 {
        match self {
            Self::C1(c) => *c.0,
        }
    }
}

#![allow(dead_code)]

pub enum E {
    A,
    B,
}

pub fn bar(x: E) {
    match x {
        E::A | E::B => (),
    }
}

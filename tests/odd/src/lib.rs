#![allow(dead_code)]

pub fn odd(n : usize) -> bool {
    !even::even(n)
}

#![allow(dead_code)]

enum Impossible {}

#[hax_lib::requires(false)]
pub fn impossible() -> Impossible {
    unsafe { std::hint::unreachable_unchecked() }
}

#[hax_lib::requires(slice.len() > 10)]
pub fn get_unchecked_example(slice: &[u8]) -> u8 {
    unsafe { *slice.get_unchecked(6) }
}

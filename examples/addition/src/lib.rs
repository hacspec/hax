use hax_lib_macros::{ensures, requires};

pub fn add(a: u32, b: u32) -> u32 {
    a + b
}

#[requires((a as u64) + (b as u64) <= 0xFFFFFFFF)]
#[ensures(|result| result == a + b)]
pub fn add_with_precondition(a: u32, b: u32) -> u32 {
    a + b
}

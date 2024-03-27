use hax_lib_macros::requires;

pub fn add(a: u8, b: u8) -> u8 {
    a + b
}

#[requires((a as u16) + (b as u16) < 256)]
pub fn add_with_precondition(a: u8, b: u8) -> u8 {
    a + b
}

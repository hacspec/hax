use hax_lib_macros::*;

#[skip]
pub fn skip_me() {}

#[hax]
pub struct Hello {
    pub x: u32,
    #[refine(y > 3)]
    pub y: u32,
    #[refine(y + x + z > 3)]
    pub z: u32,
}

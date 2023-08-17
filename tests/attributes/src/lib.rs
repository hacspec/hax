use hax_lib_macros::*;

use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug)]
pub struct SerdeTest {
    foo: u32,
}

#[skip]
pub fn f<'a, T>(c: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T {
    if c {
        x
    } else {
        y
    }
}

#[hax_attributes]
pub struct Foo {
    pub x: u32,
    #[refine(y > 3)]
    pub y: u32,
    #[refine(y + x + z > 3)]
    pub z: u32,
}

#[skip]
impl Foo {
    fn g(&self) {}
}

impl Foo {
    #[skip]
    fn h(&self) {}
}

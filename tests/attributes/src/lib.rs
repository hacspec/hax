use hax_lib_macros as hax;

// dummy max value
const u32_max: u32 = 90000;

#[hax::requires(x > 10 && y > 10 && z > 10 && x + y + z < u32_max)]
#[hax::ensures(|result| hax_lib::implies(true, || result > 32))]
fn add3(x: u32, y: u32, z: u32) -> u32 {
    x + y + z
}

#[hax::lemma]
fn add3_lemma(x: u32) -> Proof<{ x <= 10 || x >= u32_max / 3 || add3(x, x, x) == x * 3 }> {}

#[hax::exclude]
pub fn f<'a, T>(c: bool, x: &'a mut T, y: &'a mut T) -> &'a mut T {
    if c {
        x
    } else {
        y
    }
}

#[hax::attributes]
pub struct Foo {
    pub x: u32,
    #[refine(y > 3)]
    pub y: u32,
    #[refine(y + x + z > 3)]
    pub z: u32,
}

#[hax::exclude]
impl Foo {
    fn g(&self) {}
}

impl Foo {
    #[hax::exclude]
    fn h(&self) {}
}

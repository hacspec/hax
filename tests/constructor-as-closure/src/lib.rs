struct Test(i32);
impl Test {
    pub fn test(x: Option<i32>) -> Option<Test> {
        x.map(Self)
    }
}
pub enum Context {
    A(i32),
    B(i32),
}
impl Context {
    pub fn test(x: Option<i32>) -> Option<Context> {
        x.map(Self::B)
    }
}

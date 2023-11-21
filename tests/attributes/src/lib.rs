pub trait Foo: Clone {
    fn foo(&self) -> Self;
}

impl Foo for u64 {
    fn foo(&self) -> Self {
        self.clone()
    }
}

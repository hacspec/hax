//! Tests for the Rust linter
//!
//! No FnMut

trait SomeTrait {
    fn update_fun<F>(&self, fun: F) -> u8
    where
        F: FnMut(u32) -> u8;
}

struct UpdatableStruct {}

impl SomeTrait for UpdatableStruct {
    fn update_fun<F>(&self, mut fun: F) -> u8
    where
        F: FnMut(u32) -> u8,
    {
        fun(123)
    }
}

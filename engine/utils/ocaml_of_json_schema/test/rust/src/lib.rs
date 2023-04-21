use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

#[derive(JsonSchema, Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct Test {
    pub u8: u8,
    pub enum_test: Vec<EnumTest>,
}

#[derive(JsonSchema, Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum EnumTest {
    A,
    B,
    C(u8),
    D { a: u16, b: SomeStruct },
}

#[derive(JsonSchema, Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct SomeStruct {
    pub x: u32,
}

pub fn gen() -> Test {
    Test {
        u8: 123,
        enum_test: vec![
            EnumTest::B,
            EnumTest::C(32),
            EnumTest::D {
                a: 1287,
                b: SomeStruct { x: 123 },
            },
        ],
    }
}

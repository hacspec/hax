#![allow(dead_code)]

#[derive(Debug)]
pub struct Money {
    value: u64,
}

#[derive(Debug)]
pub enum EnumWithStructVariant {
    Funds { balance: Money },
}

#![allow(dead_code)]

pub fn let_else(opt: Option<u32>) -> bool {
    let Some(x) = opt else { return false };
    true
}

pub fn let_else_different_type(opt: Option<u32>) -> bool {
    let_else({
        let Some(x) = opt else { return false };
        Some(x + 1)
    })
}

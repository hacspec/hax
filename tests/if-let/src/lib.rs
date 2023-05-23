#![allow(dead_code)]

pub fn fun_with_if_let() -> u8 {
    let x = Some(5);
    if let Some(x) = x {
        x
    } else {
        7
    }
}

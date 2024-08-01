#![feature(if_let_guard)]
#![allow(dead_code)]

pub fn if_guard(x: Option<Result<i32, i32>>) -> i32 {
    match x {
        None => 0,
        Some(v) if let Ok(y) = v => y,
        Some(Err(y)) => y,
        _ => 1,
    }
}

pub fn equivalent(x: Option<Result<i32, i32>>) -> i32 {
    match x {
        None => 0,
        _ => match match x {
            Some(v) => match v {
                Ok(y) => Some(y),
                _ => None,
            },
            _ => None,
        } {
            Some(y) => y,
            None => match x {
                Some(Err(y)) => y,
                _ => 1,
            },
        },
    }
}

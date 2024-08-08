#![allow(dead_code)]
#![feature(if_let_guard)]

pub fn usize_pattern(x: usize) -> i32 {
    match x {
        1 => 1,
        2 => 2,
        _ => 0,
    }
}

pub fn u128_pattern(x: u128) -> i32 {
    match x {
        1 => 1,
        _ => 0,
    }
}

pub fn equivalent(x: usize) -> i32 {
    match x {
        a if let true = a == 1 => 1,
        a if let true = a == 2 => 2,
        _ => 0,
    }
}

pub fn usize_or_pattern(x: usize) -> i32 {
    match (x, 1) {
        (1, a) | (2, a) => a,
        _ => 0,
    }
}

pub fn usize_complicated_or_pattern(x: usize) -> usize {
    match (x, x) {
        (1, a) | (a, 1) => a,
        _ => 0,
    }
}

pub fn usize_or_equivalent(x: usize) -> i32 {
    match (x, x) {
        (a, b) if let true = (a == 1 || a == 2) => 1,
        _ => 0,
    }
}

pub fn u_i_size_nested(x1: usize, x2: usize, y: isize) -> i32 {
    match ((x1, 1), y) {
        ((1, res), 1) => res,
        _ => 0,
    }
}
pub fn u_i_size_nested_equivalent(x1: usize, x2: usize, y: isize) -> i32 {
    match ((x1, 1), y) {
        ((a1, res), b) if let (true, true) = (a1 == 1, b == 1) => res,
        _ => 0,
    }
}

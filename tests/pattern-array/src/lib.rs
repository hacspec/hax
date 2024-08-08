#![allow(dead_code)]
#![feature(if_let_guard)]

pub fn slice_pattern(x: &[i32]) -> i32 {
    match x {
        [0, .., a] => *a,
        _ => 1,
    }
}

pub fn array_pattern(x: [i32; 2]) -> i32 {
    match x {
        [0, a] => a,
        _ => 1,
    }
}

pub fn nested_array_pattern(x: &[[i32; 2]]) -> i32 {
    match x {
        [_, [y, _], ..] => *y,
        _ => 1,
    }
}

pub fn usize_array_pattern(x: &[usize]) -> usize {
    match x {
        [1, y] => *y,
        _ => 1,
    }
}

pub fn nested_usize_array_pattern(x: &[[usize; 2]]) -> usize {
    match x {
        [[1, _], [y, _], ..] => *y,
        _ => 1,
    }
}

#![allow(dead_code)]
#![feature(never_type)]

enum False {}

fn never(h: False) -> ! {
    match h {}
}

fn test(b: bool) -> u8 {
    if b {
        panic!();
    };
    3
}

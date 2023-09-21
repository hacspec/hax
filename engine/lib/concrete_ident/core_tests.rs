#![allow(dead_code)]
#![feature(try_trait_v2)]
#![feature(allocator_api)]
extern crate alloc;
/* This is a dummy Rust file. Every path used in this file will be
 * exported and made available automatically in OCaml. */

fn dummy_hax_concrete_ident_wrapper() {
    let _: Option<u8> = Some(3);
    let mut acc = vec![];
    for i in 0..10 {
        acc.push(i);
    }
    let _ = acc.iter().map(|x| x + 1);
}

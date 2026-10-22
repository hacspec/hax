//! @fail(tc): fstar(2)
//! @fail(tc): legacy-lean(1)
//! @fail(extraction): legacy-lean(HAX0001, HAX0001)
//! Trust-boundary tombstones. Each degraded item is rendered with a greppable
//! `[hax::excluded]` (signature un-stateable, definition dropped) or
//! `[hax::opaque]` (body-only failure, definition kept) marker instead of an
//! AST dump or a bare hole.

#![allow(dead_code)]

// Extracts cleanly: no tombstone.
pub fn clean_add(a: u8, b: u8) -> u8 {
    a + b
}

// A raw-pointer field cannot be stated: the whole item is excluded.
/// @fail(extraction): fstar(HAX0008), proverif(HAX0008), coq(HAX0008), legacy-lean(HAX0008), ssprove(HAX0008)
pub struct RawHolder {
    ptr: *const u8,
}

pub trait Speak {
    fn hello(&self) -> u8;
}

pub struct Cat;

impl Speak for Cat {
    fn hello(&self) -> u8 {
        1
    }
}

// `dyn` in the signature: the item cannot be stated, so it is excluded.
/// @fail(extraction): ssprove(HAX0008), proverif(HAX0008), coq(HAX0008)
pub fn dyn_in_sig(x: &dyn Speak) -> u8 {
    x.hello()
}

// `dyn` only in the body: the signature is fine, so the body is opacified.
/// @fail(extraction): proverif(HAX0008, HAX0008, HAX0008), coq(HAX0008, HAX0008, HAX0008), ssprove(HAX0008, HAX0008, HAX0008)
pub fn dyn_in_body() -> u8 {
    let c = Cat;
    let d: &dyn Speak = &c;
    d.hello()
}

// `&mut` in the return type: the item cannot be stated, so it is excluded.
/// @fail(extraction): coq(HAX0010, HAX0003), ssprove(HAX0003, HAX0010), legacy-lean(HAX0010, HAX0003), fstar(HAX0010, HAX0003), proverif(HAX0010, HAX0003)
pub fn mut_ref_return(x: &mut u8) -> &mut u8 {
    x
}

// Aliasing `&mut` in the body only: the signature is fine, so the body is opacified.
/// @fail(extraction): proverif(HAX0010, HAX0010, HAX0010, HAX0003, HAX0003, HAX0003), legacy-lean(HAX0010, HAX0010, HAX0010, HAX0003, HAX0003, HAX0003), ssprove(HAX0003, HAX0003, HAX0003, HAX0010, HAX0010, HAX0010), coq(HAX0010, HAX0010, HAX0010, HAX0003, HAX0003, HAX0003), fstar(HAX0010, HAX0010, HAX0010, HAX0003, HAX0003, HAX0003)
pub fn body_split(buf: &mut [u8]) -> u8 {
    let (a, b) = buf.split_at_mut(1);
    a[0] = b[0];
    a[0]
}

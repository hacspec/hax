//! Equivalence tests for `core::hash::*`, through client `Hasher`s that sum the
//! bytes they are fed or count the `write` calls.

use core::hash::{BuildHasher, BuildHasherDefault, Hash, Hasher};
use rust_lean_test_macro::rust_lean_test;

#[derive(Default)]
struct Sum(u64);

impl Hasher for Sum {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        let mut i = 0;
        while i < bytes.len() {
            self.0 += bytes[i] as u64;
            i += 1;
        }
    }
}

#[derive(Default)]
struct Writes(u64);

impl Hasher for Writes {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _bytes: &[u8]) {
        self.0 += 1;
    }
}

#[rust_lean_test]
pub fn test_write_u8() -> bool {
    let mut h = Sum(0);
    h.write_u8(7);
    h.finish() == 7
}

#[rust_lean_test]
pub fn test_write_u16() -> bool {
    let mut h = Sum(0);
    h.write_u16(0x0102);
    h.finish() == 3
}

#[rust_lean_test]
pub fn test_write_i32_minus_one() -> bool {
    let mut h = Sum(0);
    h.write_i32(-1);
    h.finish() == 4 * 255
}

#[rust_lean_test]
pub fn test_hash_u8() -> bool {
    let mut h = Sum(0);
    7u8.hash(&mut h);
    h.finish() == 7
}

#[rust_lean_test]
pub fn test_hash_u16() -> bool {
    let mut h = Sum(0);
    300u16.hash(&mut h);
    h.finish() == 45
}

#[rust_lean_test]
pub fn test_hash_slice_u8() -> bool {
    let mut h = Sum(0);
    Hash::hash_slice(&[1u8, 2, 3], &mut h);
    h.finish() == 6
}

#[rust_lean_test]
pub fn test_hash_slice_u16() -> bool {
    let mut h = Sum(0);
    Hash::hash_slice(&[300u16, 2], &mut h);
    h.finish() == 47
}

#[rust_lean_test]
pub fn test_hash_slice_u32_one_write() -> bool {
    let mut h = Writes(0);
    Hash::hash_slice(&[1u32, 2, 3], &mut h);
    h.finish() == 1
}

#[rust_lean_test]
pub fn test_hash_one() -> bool {
    BuildHasherDefault::<Sum>::new().hash_one(7u8) == 7
}

#[rust_lean_test]
pub fn test_build_hasher_default_default() -> bool {
    let b: BuildHasherDefault<Sum> = Default::default();
    b.hash_one(7u8) == 7
}

#[rust_lean_test]
pub fn test_build_hasher_default_clone() -> bool {
    BuildHasherDefault::<Sum>::new().clone().hash_one(300u16) == 45
}

#[rust_lean_test]
pub fn test_build_hasher_default_eq() -> bool {
    BuildHasherDefault::<Sum>::new() == BuildHasherDefault::<Sum>::default()
}

#[rust_lean_test]
pub fn test_build_hasher_default_ne() -> bool {
    !(BuildHasherDefault::<Sum>::new() != BuildHasherDefault::<Sum>::new())
}

#[rust_lean_test]
pub fn test_hash_bool() -> bool {
    let mut h = Sum(0);
    true.hash(&mut h);
    false.hash(&mut h);
    h.finish() == 1
}

#[rust_lean_test]
pub fn test_hash_str() -> bool {
    let mut h = Sum(0);
    "ab".hash(&mut h);
    h.finish() == 97 + 98 + 0xff
}

#[rust_lean_test]
pub fn test_hash_slice_type() -> bool {
    let mut h = Sum(0);
    let v: &[u16] = &[300, 2];
    v.hash(&mut h);
    h.finish() == 2 + 47
}

#[rust_lean_test]
pub fn test_hash_ref() -> bool {
    let mut h = Sum(0);
    let x = 7u8;
    (&x).hash(&mut h);
    h.finish() == 7
}

#[rust_lean_test]
pub fn test_hash_unit() -> bool {
    let mut h = Sum(0);
    ().hash(&mut h);
    h.finish() == 0
}

#[rust_lean_test]
pub fn test_hash_tuple() -> bool {
    let mut h = Sum(0);
    (1u8, true, 300u16).hash(&mut h);
    h.finish() == 1 + 1 + 45
}

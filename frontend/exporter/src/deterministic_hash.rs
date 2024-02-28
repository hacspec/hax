//! Stolen from <https://github.com/Wassasin/deterministic-hash/blob/main/src/lib.rs>
use core::hash::Hasher;

/// Wrapper around any hasher to make it deterministic.
pub struct DeterministicHasher<T: Hasher>(T);

impl<T: Hasher> DeterministicHasher<T> {
    pub fn new(inner: T) -> Self {
        Self(inner)
    }
}

/// Implementation of hasher that forces all bytes written to be platform agnostic.
impl<T: Hasher> core::hash::Hasher for DeterministicHasher<T> {
    fn finish(&self) -> u64 {
        self.0.finish()
    }

    fn write(&mut self, bytes: &[u8]) {
        self.0.write(bytes);
    }

    fn write_u8(&mut self, i: u8) {
        self.write(&i.to_le_bytes())
    }

    fn write_u16(&mut self, i: u16) {
        self.write(&i.to_le_bytes())
    }

    fn write_u32(&mut self, i: u32) {
        self.write(&i.to_le_bytes())
    }

    fn write_u64(&mut self, i: u64) {
        self.write(&i.to_le_bytes())
    }

    fn write_u128(&mut self, i: u128) {
        self.write(&i.to_le_bytes())
    }

    fn write_usize(&mut self, i: usize) {
        self.write(&(i as u64).to_le_bytes())
    }

    fn write_i8(&mut self, i: i8) {
        self.write_u8(i as u8)
    }

    fn write_i16(&mut self, i: i16) {
        self.write_u16(i as u16)
    }

    fn write_i32(&mut self, i: i32) {
        self.write_u32(i as u32)
    }

    fn write_i64(&mut self, i: i64) {
        self.write_u64(i as u64)
    }

    fn write_i128(&mut self, i: i128) {
        self.write_u128(i as u128)
    }

    fn write_isize(&mut self, i: isize) {
        self.write_usize(i as usize)
    }
}

//! This module provides an approximation of `BigInt` which is
//! copiable, via an big array of `u8` of an fixed arbitrary size
//! `BYTES`.
//! Its interface provides bridges to `num_bigint::BigInt`.

#[crate::exclude]
mod no_extraction {
    const BYTES: usize = 128;
    #[derive(Copy, Clone)]
    pub struct BigInt {
        sign: num_bigint::Sign,
        data: [u8; BYTES],
    }
    impl BigInt {
        pub fn new(i: &num_bigint::BigInt) -> Self {
            let (sign, data) = i.to_bytes_be();
            let data = data.try_into().expect(
                "`copiable_bigint::BigInt::new`: too big, please consider increasing `BYTES`",
            );
            BigInt { sign, data }
        }
        pub fn get(self) -> num_bigint::BigInt {
            num_bigint::BigInt::from_bytes_be(self.sign, &self.data)
        }
    }

    impl core::cmp::PartialEq for BigInt {
        fn eq(&self, other: &Self) -> bool {
            self.get() == other.get()
        }
    }
    impl core::cmp::Eq for BigInt {}
    impl core::cmp::Ord for BigInt {
        fn cmp(&self, other: &Self) -> core::cmp::Ordering {
            self.get().cmp(&other.get())
        }
    }
    impl core::cmp::PartialOrd for BigInt {
        fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
            self.get().partial_cmp(&other.get())
        }
    }
}

pub(super) use no_extraction::BigInt;

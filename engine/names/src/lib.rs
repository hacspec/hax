#![allow(dead_code)]
#![feature(try_trait_v2)]
#![feature(allocator_api)]

use hax_lib_protocol::cal::*;
extern crate alloc;
/* This is a dummy Rust file. Every path used in this file will be
 * exported and made available automatically in OCaml. */

fn dummy_hax_concrete_ident_wrapper<I: core::iter::Iterator<Item = u8>>(x: I, mut y: I) {
    // Crypto abstraction layer names
    let bytes = vec![0u8; 32];
    let iv = AEADIV::from_bytes(&bytes);
    let key = AEADKey::from_bytes(AEADAlgorithm::Chacha20Poly1305, &bytes);

    let (cipher_text, tag) = aead_encrypt(key, iv, &bytes, &bytes);
    let iv = AEADIV::from_bytes(&bytes);
    let key = AEADKey::from_bytes(AEADAlgorithm::Chacha20Poly1305, &bytes);
    let _ = aead_decrypt(key, iv, &bytes, &cipher_text, AEADTag::from_bytes(&bytes));

    let p = DHElement::from_bytes(&bytes);
    let s = DHScalar::from_bytes(&bytes);
    dh_scalar_multiply(DHGroup::X25519, s.clone(), p);
    dh_scalar_multiply_base(DHGroup::X25519, s);

    let _ = hmac(HMACAlgorithm::Sha256, &bytes, &bytes);

    let _ = 1u64.to_le_bytes();

    let _ = hash(HashAlgorithm::Sha256, &bytes);
    let _ = cipher_text.clone();
    // End crypto abstractions example

    let _: core::result::Result<u8, u8> = core::result::Result::Ok(0);
    let _: core::result::Result<u8, u8> = core::result::Result::Err(0);
    let _ = x.fold(0, |a, b| a + b);
    let _ = y.next();
    let _: core::ops::ControlFlow<u8> = core::ops::ControlFlow::Break(0);
    let _: core::ops::ControlFlow<u8> = core::ops::ControlFlow::Continue(());
    let mut v = vec![()];
    v[0];
    v[0] = ();
    use std::ops::FromResidual;
    let _ = Result::<String, i64>::from_residual(Err(3u8));
    let _ = Box::new(());
    let _: Option<alloc::alloc::Global> = None;
    let _: Option<()> = Some(());
    let _: Option<()> = None;
    let _: Result<(), u32> = Result::Err(3u8).map_err(u32::from);

    let _ = [()].into_iter();
    let _ = 1..2;
    let _ = 1..;
    let _ = ..;
    let _ = ..1;

    fn question_mark_result<A, B: From<A>>(x: A) -> Result<(), B> {
        Err(x)?;
        Ok(())
    }

    const _: () = {
        use core::{cmp::*, ops::*};
        fn arith<
            X: Add<Output = X>
                + Sub<Output = X>
                + Mul<Output = X>
                + Div<Output = X>
                + Rem<Output = X>
                + BitXor<Output = X>
                + BitAnd<Output = X>
                + BitOr<Output = X>
                + Shl<Output = X>
                + Shr<Output = X>
                + Neg<Output = X>
                + Not<Output = X>
                + PartialOrd
                + Copy,
        >(
            x: X,
        ) -> X {
            let _ = x < x && x > x && x <= x && x >= x && x == x && x != x;
            (x ^ x & !x) + x / x * x - x | (-x) % x << x >> x
        }
    };

    fn dummy<T: core::ops::Try<Output = ()>>(z: T) {
        let _ = T::from_output(());
        let _ = z.branch();
    }

    let s: &str = "123";
    let ptr: *const u8 = s.as_ptr();

    unsafe {
        let _ = *ptr.offset(1) as char;
    }

    const _: () = {
        use std::ops::DerefMut;
        fn f<T: DerefMut>(x: T) {
            let _: &mut _ = { x }.deref_mut();
        }
    };
}

macro_rules! impl_arith {
    ($name:ident$(,)?) => {
        mod $name {
            fn add() {}
            fn sub() {}
            fn mul() {}
            fn div() {}
            fn rem() {}
            fn bit_xor() {}
            fn bit_and() {}
            fn bit_or() {}
            fn shl() {}
            fn shr() {}
            fn eq() {}
            fn lt() {}
            fn le() {}
            fn ne() {}
            fn ge() {}
            fn gt() {}
        }
    };
    ($name:ident,$($rest:tt)*) => {
        impl_arith!($name);
        impl_arith!($($rest)*);
    }
}

impl_arith!(u128);
// impl_arith!(u8, u16, u32, u64, u128, usize);
// impl_arith!(i8, i16, i32, i64, i128, isize);

fn offset() {}

fn unsize() {}

/// Hax additions
mod hax {
    fn failure() {}
    struct Failure;
    enum Never {}

    // Only useful when HAX_CORE_EXTRACTION_MODE in `on`
    enum MutRef {}

    fn repeat() {}
    fn update_at() {}
    mod monomorphized_update_at {
        fn update_at_usize() {}
        fn update_at_range() {}
        fn update_at_range_from() {}
        fn update_at_range_to() {}
        fn update_at_range_full() {}
    }
    // TODO: Should that live here? (this is F* specific)
    fn array_of_list() {}
    fn never_to_any() {}

    mod control_flow_monad {
        trait ControlFlowMonad {
            fn lift() {}
        }
        mod mexception {
            fn run() {}
        }
        mod mresult {
            fn run() {}
        }
        mod moption {
            fn run() {}
        }
    }
    fn box_new() {}
}

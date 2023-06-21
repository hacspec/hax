#![allow(dead_code)]
#![feature(try_trait_v2)]
#![feature(allocator_api)]
extern crate alloc;
/* This is a dummy Rust file. Every path used in this file will be
 * exported and made available automatically in OCaml. */

fn dummy_hax_concrete_ident_wrapper<I: core::iter::Iterator<Item = u8>>(x: I, mut y: I) {
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

    let _ = [()].into_iter();
    let _ = 1..2;

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
}

mod error {
    fn failure() {}
    struct Failure;
}
pub trait Array {
    fn repeat() {}
    fn update_at() {}
    fn array_of_list() {}
}
// pub trait Array<Idx>: core::ops::Index<Idx> {
//     fn update_at(&self, _index: Idx) -> &Self::Output {
//         panic!()
//     }
// }
trait CoerceUnsize {
    fn unsize() {}
}

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

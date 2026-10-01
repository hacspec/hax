#![allow(unused_variables)]

use super::marker::Copy;

/// See [`std::mem::forget`]
#[hax_lib::opaque]
// mutants::skip: forgetting has no observable effect, so replacing the body with () is an equivalent mutant.
#[cfg_attr(test, mutants::skip)]
pub fn forget<T>(t: T) {
    rust_primitives::mem::forget(t)
}

/// See [`std::mem::forget_unsized`]
#[hax_lib::opaque]
// mutants::skip: as for `forget`, the empty body is an equivalent mutant.
#[cfg_attr(test, mutants::skip)]
pub fn forget_unsized<T>(t: T) {
    rust_primitives::mem::forget(t)
}

/// See [`std::mem::size_of`]
#[hax_lib::opaque]
pub fn size_of<T>() -> usize {
    rust_primitives::mem::size_of::<T>()
}

/// See [`std::mem::size_of_val`]
#[hax_lib::opaque]
pub fn size_of_val<T: ?Sized>(val: &T) -> usize {
    rust_primitives::mem::size_of_val(val)
}

/// See [`std::mem::min_align_of`]
#[hax_lib::opaque]
pub fn min_align_of<T>() -> usize {
    rust_primitives::mem::align_of::<T>()
}

/// See [`std::mem::min_align_of_val`]
#[hax_lib::opaque]
pub fn min_align_of_val<T: ?Sized>(val: &T) -> usize {
    rust_primitives::mem::align_of_val(val)
}

/// See [`std::mem::align_of`]
#[hax_lib::opaque]
pub fn align_of<T>() -> usize {
    rust_primitives::mem::align_of::<T>()
}

/// See [`std::mem::align_of_val`]
#[hax_lib::opaque]
pub fn align_of_val<T: ?Sized>(val: &T) -> usize {
    rust_primitives::mem::align_of_val(val)
}

/// See [`std::mem::align_of_val_raw`]
// Excluded from coverage: unlike std's, this signature takes the value itself
// rather than a raw pointer, so there is no callable meaning to give it.
#[cfg_attr(coverage_nightly, coverage(off))]
#[hax_lib::opaque]
pub unsafe fn align_of_val_raw<T>(val: T) -> usize {
    panic!()
}

/// See [`std::mem::needs_drop`]
#[hax_lib::opaque]
pub fn needs_drop<T: ?Sized>() -> bool {
    rust_primitives::mem::needs_drop::<T>()
}

/// See [`std::mem::uninitialized`]
// Excluded from coverage: calling it is instant UB, so no test may run it.
#[cfg_attr(coverage_nightly, coverage(off))]
#[hax_lib::opaque]
#[hax_lib::requires(false)]
pub unsafe fn uninitialized<T>() -> T {
    panic!()
}

/// See [`std::mem::swap`]
#[cfg_attr(hax_backend_lean, hax_lib::exclude)]
#[hax_lib::opaque]
pub fn swap<T>(x: &mut T, y: &mut T) {
    rust_primitives::mem::swap(x, y)
}

/// See [`std::mem::replace`]
#[cfg_attr(hax_backend_lean, hax_lib::exclude)]
#[hax_lib::opaque]
pub fn replace<T>(dest: &mut T, mut src: T) -> T {
    swap(dest, &mut src);
    src
}

/// See [`std::mem::drop`]
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
pub fn drop<T>(_x: T) {}

/// See [`std::mem::take`]
// Excluded from coverage: std's `take` needs `T: Default` to leave something
// behind in `*x`; this signature has no such bound, so it cannot be written.
#[cfg_attr(coverage_nightly, coverage(off))]
#[hax_lib::opaque]
pub unsafe fn take<T>(x: &mut T) -> T {
    panic!()
}

/// See [`std::mem::transmute_copy`]
#[hax_lib::opaque]
#[hax_lib::requires(false)]
pub unsafe fn transmute_copy<Src, Dst>(src: &Src) -> Dst {
    unsafe { rust_primitives::mem::transmute_copy(src) }
}

/// See [`std::mem::variant_count`]
// Excluded from coverage: `core::mem::variant_count` is a nightly-only
// intrinsic, and `rust_primitives` must keep building on stable.
#[cfg_attr(coverage_nightly, coverage(off))]
#[hax_lib::opaque]
// mutants::skip: excluded from coverage above, so no test can kill a mutant here.
#[cfg_attr(test, mutants::skip)]
pub fn variant_count<T>() -> usize {
    panic!()
}

/// See [`std::mem::zeroed`]
#[hax_lib::opaque]
#[hax_lib::requires(false)]
pub unsafe fn zeroed<T>() -> T {
    unsafe { rust_primitives::mem::zeroed() }
}

/// See [`std::mem::transmute`]
#[hax_lib::opaque]
#[hax_lib::requires(false)]
pub unsafe fn transmute<Src, Dst>(src: Src) -> Dst {
    unsafe { rust_primitives::mem::transmute(src) }
}

/// See [`std::mem::copy`]
pub fn copy<T: crate::marker::Copy>(x: &T) -> T {
    crate::clone::Clone::clone(x)
}

/// See [`std::mem::conjure_zst`]
// Opaque: sound only for an inhabited zero-sized `T`, which the model cannot state.
#[cfg_attr(coverage_nightly, coverage(off))]
#[hax_lib::opaque]
pub unsafe fn conjure_zst<T>() -> T {
    panic!()
}

/// See [`std::mem::size_of_val_raw`]
// Excluded from F*, which has no raw pointers; the body needs a layout.
#[cfg_attr(coverage_nightly, coverage(off))]
#[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
#[cfg_attr(hax_backend_lean, hax_lib::opaque)]
pub unsafe fn size_of_val_raw<T: ?Sized>(val: *const T) -> usize {
    panic!()
}

mod manually_drop {
    /// See [`std::mem::ManuallyDrop`]
    pub struct ManuallyDrop<T: ?Sized> {
        value: T,
    }

    impl<T> ManuallyDrop<T> {
        /// See [`std::mem::ManuallyDrop::new`]
        pub fn new(value: T) -> ManuallyDrop<T> {
            ManuallyDrop { value }
        }

        /// See [`std::mem::ManuallyDrop::into_inner`]
        pub fn into_inner(slot: ManuallyDrop<T>) -> T {
            slot.value
        }

        /// See [`std::mem::ManuallyDrop::take`]
        // Opaque: without raw pointers there is no way to move a `T` out of the slot.
        #[cfg_attr(coverage_nightly, coverage(off))]
        #[hax_lib::opaque]
        pub unsafe fn take(slot: &mut ManuallyDrop<T>) -> T {
            panic!()
        }
    }

    impl<T: ?Sized> ManuallyDrop<T> {
        /// See [`std::mem::ManuallyDrop::drop`]
        pub unsafe fn drop(slot: &mut ManuallyDrop<T>) {}
    }
}

mod maybe_dangling {
    /// See [`std::mem::MaybeDangling`]
    pub struct MaybeDangling<P: ?Sized>(P);

    impl<P: ?Sized> MaybeDangling<P> {
        /// See [`std::mem::MaybeDangling::new`]
        pub fn new(x: P) -> Self
        where
            P: Sized,
        {
            MaybeDangling(x)
        }

        /// See [`std::mem::MaybeDangling::as_ref`]
        pub fn as_ref(&self) -> &P {
            &self.0
        }

        /// See [`std::mem::MaybeDangling::as_mut`]
        // Not in F*: hax rejects a `&mut` into a field (hacspec/hax#420).
        #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
        pub fn as_mut(&mut self) -> &mut P {
            &mut self.0
        }

        /// See [`std::mem::MaybeDangling::into_inner`]
        pub fn into_inner(self) -> P
        where
            P: Sized,
        {
            self.0
        }
    }
}

mod drop_guard {
    /// See [`std::mem::DropGuard`]
    // DEVIATION(std): no `ManuallyDrop` fields (no destructors) and no `F: FnOnce(T)`
    // bound on the struct, which F* would turn into a refinement argument of the type.
    pub struct DropGuard<T, F> {
        inner: T,
        f: F,
    }

    impl<T, F: FnOnce(T)> DropGuard<T, F> {
        /// See [`std::mem::DropGuard::new`]
        pub fn new(inner: T, f: F) -> Self {
            DropGuard { inner, f }
        }

        /// See [`std::mem::DropGuard::dismiss`]
        pub fn dismiss(guard: Self) -> T {
            guard.inner
        }
    }
}

#[cfg(test)]
mod tests {
    use super::drop_guard::DropGuard;
    use super::manually_drop::ManuallyDrop;
    use super::maybe_dangling::MaybeDangling;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_copy(x in any::<u32>()) {
            prop_assert_eq!(super::copy(&x), core::mem::copy(&x));
        }

        #[test]
        fn test_manually_drop_round_trip(x in any::<u32>()) {
            prop_assert_eq!(
                ManuallyDrop::into_inner(ManuallyDrop::new(x)),
                core::mem::ManuallyDrop::into_inner(core::mem::ManuallyDrop::new(x))
            );
        }

        #[test]
        fn test_manually_drop_drop_is_noop(x in any::<u32>()) {
            let mut model = ManuallyDrop::new(x);
            unsafe { ManuallyDrop::drop(&mut model) };
            let mut std_slot = core::mem::ManuallyDrop::new(x);
            unsafe { core::mem::ManuallyDrop::drop(&mut std_slot) };
            prop_assert_eq!(
                ManuallyDrop::into_inner(model),
                core::mem::ManuallyDrop::into_inner(std_slot)
            );
        }

        // `core::mem::MaybeDangling` is not on this toolchain, so these pin the behaviour.
        #[test]
        fn test_maybe_dangling_round_trip(x in any::<u32>()) {
            prop_assert_eq!(MaybeDangling::new(x).into_inner(), x);
        }

        #[test]
        fn test_maybe_dangling_as_ref(x in any::<u32>()) {
            prop_assert_eq!(*MaybeDangling::new(x).as_ref(), x);
        }

        #[test]
        fn test_maybe_dangling_as_mut(x in any::<u32>(), y in any::<u32>()) {
            let mut m = MaybeDangling::new(x);
            *m.as_mut() = y;
            prop_assert_eq!(m.into_inner(), y);
        }

        // Not compared with std: the accessor's name differs between the CI nightlies.
        #[test]
        fn test_drop_guard_dismiss(x in any::<u32>()) {
            prop_assert_eq!(DropGuard::dismiss(DropGuard::new(x, |_: u32| ())), x);
        }
    }

    use proptest::prelude::*;

    // Layout queries take no runtime input, so they are checked per type
    // against `std::mem` rather than over a proptest domain.
    macro_rules! layout_tests {
        ($($t:ident),*) => {
            pastey::paste! { $(
                #[test]
                fn [<test_size_of_ $t>]() {
                    assert_eq!(super::size_of::<$t>(), std::mem::size_of::<$t>());
                }
                #[test]
                fn [<test_align_of_ $t>]() {
                    assert_eq!(super::align_of::<$t>(), std::mem::align_of::<$t>());
                    assert_eq!(super::min_align_of::<$t>(), std::mem::align_of::<$t>());
                }
                #[test]
                fn [<test_needs_drop_ $t>]() {
                    assert_eq!(super::needs_drop::<$t>(), std::mem::needs_drop::<$t>());
                }
            )* }
        };
    }

    layout_tests!(
        u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize, bool
    );

    #[test]
    fn test_needs_drop_string() {
        assert_eq!(
            super::needs_drop::<std::string::String>(),
            std::mem::needs_drop::<std::string::String>()
        );
    }

    proptest! {
        #[test]
        fn test_size_of_val(v in prop::collection::vec(any::<u8>(), 0..50)) {
            prop_assert_eq!(super::size_of_val(v.as_slice()), std::mem::size_of_val(v.as_slice()));
            prop_assert_eq!(
                super::min_align_of_val(v.as_slice()),
                std::mem::align_of_val(v.as_slice())
            );
            prop_assert_eq!(
                super::align_of_val(v.as_slice()),
                std::mem::align_of_val(v.as_slice())
            );
        }

        // A wider element type: with `u8` slices every alignment is 1, which
        // any wrong answer of 1 also satisfies.
        #[test]
        fn test_align_of_val_wide(v in prop::collection::vec(any::<u64>(), 1..50)) {
            prop_assert_eq!(
                super::align_of_val(v.as_slice()),
                std::mem::align_of_val(v.as_slice())
            );
            prop_assert_eq!(
                super::min_align_of_val(v.as_slice()),
                std::mem::align_of_val(v.as_slice())
            );
        }

        #[test]
        fn test_swap(x in any::<u32>(), y in any::<u32>()) {
            let (mut ma, mut mb) = (x, y);
            super::swap(&mut ma, &mut mb);
            let (mut sa, mut sb) = (x, y);
            std::mem::swap(&mut sa, &mut sb);
            prop_assert_eq!((ma, mb), (sa, sb));
        }

        #[test]
        fn test_replace(dest in any::<u32>(), src in any::<u32>()) {
            let mut md = dest;
            let mold = super::replace(&mut md, src);
            let mut sd = dest;
            let sold = std::mem::replace(&mut sd, src);
            prop_assert_eq!((mold, md), (sold, sd));
        }

        #[test]
        fn test_forget(x in any::<u32>()) {
            // `forget` is observationally a no-op for a `Copy` value; what is
            // checked is that it consumes its argument without panicking.
            super::forget(x);
            super::forget_unsized(x);
            super::drop(x);
            prop_assert_eq!(x, x);
        }

        #[test]
        fn test_zeroed(_ignored in any::<u8>()) {
            prop_assert_eq!(unsafe { super::zeroed::<u32>() }, unsafe { std::mem::zeroed::<u32>() });
        }

        #[test]
        fn test_transmute(x in any::<u32>()) {
            prop_assert_eq!(unsafe { super::transmute::<u32, [u8; 4]>(x) }, x.to_ne_bytes());
        }

        #[test]
        fn test_transmute_copy(x in any::<u32>()) {
            prop_assert_eq!(
                unsafe { super::transmute_copy::<u32, [u8; 4]>(&x) },
                x.to_ne_bytes()
            );
        }
    }
}

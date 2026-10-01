// In F* we replace the definition to have the equality a value
// and its clone, and every type is clonable there.
/// See [`std::clone::Clone`]
#[hax_lib::fstar::replace(
    "class t_Clone self = {
  f_clone_pre: self -> Type0;
  f_clone_post: self -> self -> Type0;
  f_clone: x:self -> r:self {x == r}
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let clone_identity (#v_T: Type0) : t_Clone v_T =
  {
    f_clone_pre = (fun (self: v_T) -> true);
    f_clone_post = (fun (self: v_T) (out: v_T) -> true);
    f_clone = fun (self: v_T) -> self
  }"
)]
pub trait Clone {
    /// See [`std::clone::Clone::clone`]
    fn clone(&self) -> Self;

    /// See [`std::clone::Clone::clone_from`]
    #[cfg(not(hax_backend_fstar))]
    fn clone_from(self, source: Self) -> Self
    where
        Self: Sized,
    {
        source.clone()
    }
}

// Rust's `Clone`: an arbitrary `T` cannot produce an owned `Self` from `&self`.
#[cfg(hax_backend_fstar)]
#[hax_lib::exclude]
impl<T: core::clone::Clone> Clone for T {
    fn clone(&self) -> Self {
        core::clone::Clone::clone(self)
    }
}

// Not `unsafe` as in real core: a pure model has no unsafe obligation.
/// See [`std::clone::TrivialClone`]
pub trait TrivialClone: Clone {}

/// See [`std::clone::UseCloned`]
pub trait UseCloned: Clone {}

// Under F*, `Clone` is the identity on every type, so both markers hold everywhere.
#[cfg(hax_backend_fstar)]
impl<T: core::clone::Clone> TrivialClone for T {}
#[cfg(hax_backend_fstar)]
impl<T: core::clone::Clone> UseCloned for T {}

macro_rules! clone_impl_for_copy {
    ($($t:ty),*) => {
        $(
            impl crate::clone::Clone for $t {
                fn clone(&self) -> Self {
                    *self
                }
            }
            impl crate::clone::TrivialClone for $t {}
            impl crate::clone::UseCloned for $t {}
        )*
    };
}

#[cfg(not(hax_backend_fstar))]
clone_impl_for_copy!(
    core::primitive::bool,
    core::primitive::u8,
    core::primitive::u16,
    core::primitive::u32,
    core::primitive::u64,
    core::primitive::u128,
    core::primitive::usize,
    core::primitive::i8,
    core::primitive::i16,
    core::primitive::i32,
    core::primitive::i64,
    core::primitive::i128,
    core::primitive::isize
);

#[cfg(test)]
mod tests {
    use crate::testing::Inject;
    use pastey::paste;
    use proptest::prelude::*;

    fn clone_trivial<T: crate::clone::TrivialClone>(x: &T) -> T {
        crate::clone::Clone::clone(x)
    }

    fn clone_used<T: crate::clone::UseCloned>(x: &T) -> T {
        crate::clone::Clone::clone(x)
    }

    // For every `Copy` type with a `Clone` impl, check the model's `Clone`
    // agrees with std's on a random value.
    macro_rules! clone_tests {
        ($($t:ident),*) => {
            paste! { $(
                proptest! {
                    #[test]
                    fn [<test_clone_ $t>](x in any::<$t>()) {
                        prop_assert_eq!(crate::clone::Clone::clone(&x.inject()), x.clone().inject());
                    }

                    // Pinned against std's `Clone`: its markers are unavailable here.
                    #[test]
                    fn [<test_trivial_clone_ $t>](x in any::<$t>()) {
                        prop_assert_eq!(clone_trivial(&x.inject()), x.clone().inject());
                    }

                    #[test]
                    fn [<test_use_cloned_ $t>](x in any::<$t>()) {
                        prop_assert_eq!(clone_used(&x.inject()), x.clone().inject());
                    }

                    #[cfg(not(hax_backend_fstar))]
                    #[test]
                    fn [<test_clone_from_ $t>](x in any::<$t>(), y in any::<$t>()) {
                        let mut std_dst = x;
                        std::clone::Clone::clone_from(&mut std_dst, &y);
                        prop_assert_eq!(
                            crate::clone::Clone::clone_from(x.inject(), y.inject()),
                            std_dst.inject()
                        );
                    }
                }
            )* }
        };
    }

    clone_tests!(
        bool, u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
    );
}

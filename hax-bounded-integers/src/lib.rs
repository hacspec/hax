use hax_lib::Refinement;
pub mod num_traits;

#[doc(hidden)]
#[macro_export]
macro_rules! derivate_binop_for_bounded {
    ($(<$(const $cst_name:ident : $cst_ty:ty),*>)?{$t:ident, $bounded_t:ident}; $($tt:tt)*) => {
        $crate::derivate_binop_for_bounded!($(<$(const $cst_name:$cst_ty),*>)?{$t, $bounded_t, get, Self::Output}; $($tt)*) ;
    };
    ($(<$(const $cst_name:ident : $cst_ty:ty),*>)?{$t:ident, $bounded_t:ident, $get:ident, $out:ty};) => {};
    ($(<$(const $cst_name:ident : $cst_ty:ty),*>)?{$t:ident, $bounded_t:ident, $get:ident, $out:ty}; ($trait:ident, $meth:ident), $($tt:tt)*) => {
        $crate::derivate_binop_for_bounded!(@$t, $bounded_t, $trait, $meth, $get, $out, $(<$(const $cst_name:$cst_ty),*>)?);
        $crate::derivate_binop_for_bounded!($(<$(const $cst_name:$cst_ty),*>)?{$t, $bounded_t, $get, $out}; $($tt)*);
    };
    (@$t:ident, $bounded_t:ident, $trait:ident, $meth:ident, $get:ident, $out:ty$(,)?) => {
        $crate::derivate_binop_for_bounded!(
            @$t, $bounded_t, $trait, $meth, $get, $out,
            <const MIN: $t, const MAX: $t>
        );
    };
    (@$t:ident, $bounded_t:ident, $trait:ident, $meth:ident, $get:ident, $out:ty,
     <$(const $cst_name:ident : $cst_ty:ty),*>
    ) => {
        paste::paste!{
            // BoundedT<A, B> <OP> BoundedT<C, D>
            impl<$(const [< $cst_name _LHS >]: $cst_ty,)* $(const [< $cst_name _RHS >]: $cst_ty,)*>
                $trait<$bounded_t<$([< $cst_name _RHS >],)*>> for $bounded_t<$([< $cst_name _LHS >],)*>
            {
                type Output = $t;
                #[inline(always)]
                fn $meth(self, other: $bounded_t<$([< $cst_name _RHS >],)*>) -> $out {
                    (self.$get()).$meth(other.$get())
                }
            }

            // BoundedT<A, B> <OP> T
            impl<$(const $cst_name: $cst_ty,)*> $trait<$t> for $bounded_t<$($cst_name,)*> {
                type Output = $t;
                #[inline(always)]
                fn $meth(self, other: $t) -> $out {
                    (self.$get()).$meth(other)
                }
            }


            // T <OP> BoundedT<A, B>
            impl<$(const $cst_name: $cst_ty,)*> $trait<$bounded_t<$($cst_name,)*>> for $t {
                type Output = $t;
                #[inline(always)]
                fn $meth(self, other: $bounded_t<$($cst_name,)*>) -> $out {
                    (self).$meth(other.$get())
                }
            }
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! derivate_assign_binop_for_bounded {
    ($(<$(const $cst_name:ident : $cst_ty:ty),*>)?{$t:ident, $bounded_t:ident}; $($tt:tt)*) => {
        $crate::derivate_assign_binop_for_bounded!($(<$(const $cst_name:$cst_ty),*>)?{$t, $bounded_t, get, Self::Output}; $($tt)*) ;
    };
    ($(<$(const $cst_name:ident : $cst_ty:ty),*>)?{$t:ident, $bounded_t:ident, $get:ident, $out:ty};) => {};
    ($(<$(const $cst_name:ident : $cst_ty:ty),*>)?{$t:ident, $bounded_t:ident, $get:ident, $out:ty}; ($trait:ident, $meth:ident), $($tt:tt)*) => {
        $crate::derivate_assign_binop_for_bounded!(@$t, $bounded_t, $trait, $meth, $get, $out, $(<$(const $cst_name:$cst_ty),*>)?);
        $crate::derivate_assign_binop_for_bounded!($(<$(const $cst_name:$cst_ty),*>)?{$t, $bounded_t, $get, $out}; $($tt)*);
    };
    (@$t:ident, $bounded_t:ident, $trait:ident, $meth:ident, $get:ident, $out:ty$(,)?) => {
        $crate::derivate_assign_binop_for_bounded!(
            @$t, $bounded_t, $trait, $meth, $get, $out,
            <const MIN: $t, const MAX: $t>
        );
    };
    (@$t:ident, $bounded_t:ident, $trait:ident, $meth:ident, $get:ident, $out:ty,
     <$(const $cst_name:ident : $cst_ty:ty),*>
    ) => {
        paste::paste!{
            // BoundedT<A, B> <OP> BoundedT<C, D>
            impl<$(const [< $cst_name _LHS >]: $cst_ty,)* $(const [< $cst_name _RHS >]: $cst_ty,)*>
                $trait<$bounded_t<$([< $cst_name _RHS >],)*>> for $bounded_t<$([< $cst_name _LHS >],)*>
            {
                #[inline(always)]
                fn $meth(&mut self, other: $bounded_t<$([< $cst_name _RHS >],)*>) {
                    self.get_mut().$meth(other.$get())
                }
            }

            // BoundedT<A, B> <OP> $t
            impl<$(const [< $cst_name _LHS >]: $cst_ty,)*>
                $trait<$t> for $bounded_t<$([< $cst_name _LHS >],)*>
            {
                #[inline(always)]
                fn $meth(&mut self, other: $t) {
                    self.get_mut().$meth(other)
                }
            }

            // $t <OP> BoundedT<A, B>
            impl<$(const [< $cst_name _RHS >]: $cst_ty,)*>
                $trait<$bounded_t<$([< $cst_name _RHS >],)*>> for $t
            {
                #[inline(always)]
                fn $meth(&mut self, other: $bounded_t<$([< $cst_name _RHS >],)*>) {
                    self.$meth(other.get())
                }
            }
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! derivate_operations_for_bounded {
    ($bounded_t:ident($t: ident $($bytes:expr)?)$(,)?
     <$(const $cst_name:ident : $cst_ty:ty),*>
    ) => {
          #[duplicate::duplicate_item(
              INTRO_CONSTANTS USE_CONSTANTS;
              [ $(const $cst_name:$cst_ty),* ] [ $($cst_name),* ];
          )]
          #[hax_lib::exclude]
        const _: () = {
            use ::core::ops::*;
            use $crate::num_traits::*;
            use ::hax_lib::Refinement;

            $crate::derivate_assign_binop_for_bounded!(
                <INTRO_CONSTANTS>
                {$t, $bounded_t};
                (AddAssign, add_assign),
                (SubAssign, sub_assign),
                (MulAssign, mul_assign),
                (DivAssign, div_assign),
                (RemAssign, rem_assign),
                (ShlAssign, shl_assign),
                (ShrAssign, shr_assign),
                (BitAndAssign, bitand_assign),
                (BitOrAssign, bitor_assign),
                (BitXorAssign, bitxor_assign),
            );

            $crate::derivate_binop_for_bounded!(
                <INTRO_CONSTANTS>
                {$t, $bounded_t};
                (Add, add), (Sub, sub), (Mul, mul), (Div, div), (Rem, rem),
                (BitOr, bitor), (BitAnd, bitand), (BitXor, bitxor),
                (Shl, shl), (Shr, shr),
                (WrappingAdd, wrapping_add), (WrappingSub, wrapping_sub),
                (WrappingMul, wrapping_mul), (WrappingDiv, wrapping_div),
            );

            $crate::derivate_binop_for_bounded!(
                <INTRO_CONSTANTS>
                {$t, $bounded_t, get, Option<Self::Output>};
                (CheckedAdd, checked_add), (CheckedSub, checked_sub),
                (CheckedMul, checked_mul), (CheckedDiv, checked_div),
            );

            impl<INTRO_CONSTANTS> CheckedNeg for $bounded_t<USE_CONSTANTS> {
                type Output = $t;
                #[inline(always)]
                fn checked_neg(&self) -> Option<$t> {
                    self.deref().checked_neg()
                }
            }

            impl<INTRO_CONSTANTS> Not for $bounded_t<USE_CONSTANTS> {
                type Output = $t;
                #[inline(always)]
                fn not(self) -> Self::Output {
                    self.deref().not()
                }
            }

            impl<INTRO_CONSTANTS> NumOps<Self, $t> for $bounded_t<USE_CONSTANTS> {}

            // impl<INTRO_CONSTANTS> Bounded for $bounded_t<USE_CONSTANTS> {
            //     #[inline(always)]
            //     fn min_value() -> Self {
            //         Self::new(MIN)
            //     }
            //     #[inline(always)]
            //     fn max_value() -> Self {
            //         Self::new(MAX)
            //     }
            // }

            $(
                impl<INTRO_CONSTANTS> FromBytes for $bounded_t<USE_CONSTANTS> {
                    type BYTES = [u8; $bytes];

                    #[inline(always)]
                    fn from_le_bytes(bytes: Self::BYTES) -> Self {
                        Self::new($t::from_le_bytes(bytes))
                    }
                    #[inline(always)]
                    fn from_be_bytes(bytes: Self::BYTES) -> Self {
                        Self::new($t::from_be_bytes(bytes))
                    }
                }

                impl<INTRO_CONSTANTS> ToBytes for $bounded_t<USE_CONSTANTS> {
                    #[inline(always)]
                    fn to_le_bytes(self) -> Self::BYTES {
                        self.get().to_le_bytes()
                    }
                    #[inline(always)]
                    fn to_be_bytes(self) -> Self::BYTES {
                        self.get().to_be_bytes()
                    }
                }
            )?

            impl<INTRO_CONSTANTS> Zero for $bounded_t<USE_CONSTANTS> {
                #[inline(always)]
                fn zero() -> Self {
                    Self::new(0)
                }
            }

            impl<INTRO_CONSTANTS> One for $bounded_t<USE_CONSTANTS> {
                #[inline(always)]
                fn one() -> Self {
                    Self::new(1)
                }
            }

            impl<INTRO_CONSTANTS> MachineInt<$t> for $bounded_t<USE_CONSTANTS> { }

            impl<INTRO_CONSTANTS> BitOps for $bounded_t<USE_CONSTANTS> {
                type Output = $t;

                #[inline(always)]
                fn count_ones(self) -> u32 {
                    self.get().count_ones()
                }
                #[inline(always)]
                fn count_zeros(self) -> u32 {
                    self.get().count_zeros()
                }
                #[inline(always)]
                fn leading_ones(self) -> u32 {
                    self.get().leading_ones()
                }
                #[inline(always)]
                fn leading_zeros(self) -> u32 {
                    self.get().leading_zeros()
                }
                #[inline(always)]
                fn trailing_ones(self) -> u32 {
                    self.get().trailing_ones()
                }
                #[inline(always)]
                fn trailing_zeros(self) -> u32 {
                    self.get().trailing_zeros()
                }
                #[inline(always)]
                fn rotate_left(self, n: u32) -> Self::Output {
                    self.get().rotate_left(n)
                }
                #[inline(always)]
                fn rotate_right(self, n: u32) -> Self::Output {
                    self.get().rotate_right(n)
                }
                #[inline(always)]
                fn from_be(x: Self) -> Self::Output {
                    Self::Output::from_be(x.get())
                }
                #[inline(always)]
                fn from_le(x: Self) -> Self::Output {
                    Self::Output::from_le(x.get())
                }
                #[inline(always)]
                fn to_be(self) -> Self::Output {
                    Self::Output::to_be(self.get())
                }
                #[inline(always)]
                fn to_le(self) -> Self::Output {
                    Self::Output::to_le(self.get())
                }
                #[inline(always)]
                fn pow(self, exp: u32) -> Self::Output {
                    Self::Output::pow(self.get(), exp)
                }
            }
        };
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! mk_bounded {
    ($(#$attr:tt)* $bounded_t:ident<$(const $cst_name:ident : $cst_ty:ty),*>($t: ident $($bytes:expr)?, |$x:ident| $body:expr)$(,)?) => {
        #[hax_lib::refinement_type(|$x| $body)]
        #[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
        $(#$attr)*
        pub struct $bounded_t<$(const $cst_name : $cst_ty),*>($t);
        $crate::derivate_operations_for_bounded!($bounded_t($t$($bytes)?)<$(const $cst_name : $cst_ty),*>);
    };
    ($bounded_t:ident($t: ident $($bytes:expr)?)$(,)?) => {
        $crate::mk_bounded!(
            #[doc = concat!("Bounded ", stringify!($t)," integers. This struct enforces the invariant that values are greater or equal to `MIN` and less or equal to `MAX`.")]
            $bounded_t<const MIN: $t, const MAX: $t>($t $($bytes)?, |x| x >= MIN && x <= MAX)
        );
    };
    ($bounded_t:ident($t: ident $($bytes:expr)?), $($tt:tt)+) => {
        $crate::mk_bounded!($bounded_t($t $($bytes)?));
        $crate::mk_bounded!($($tt)+);
    };
}

mk_bounded!(
    BoundedI8(i8 1),
    BoundedI16(i16 2),
    BoundedI32(i32 4),
    BoundedI64(i64 8),
    BoundedI128(i128 16),
    BoundedIsize(isize),
    BoundedU8(u8 1),
    BoundedU16(u16 2),
    BoundedU32(u32 4),
    BoundedU64(u64 8),
    BoundedU128(u128 16),
    BoundedUsize(usize),
);

/// Makes a refined new type in a very similar way to
/// `hax_lib::refinement_tyoe`, but derives the various traits an
/// integer type is expected to implement.
///
/// Examples:
/// ```rust
/// # use hax_bounded_integers::refinement_int;
/// refinement_int!(BoundedAbsI16<const B: usize>(i16, 2, |x| x >= -(B as i16) && x <= (B as i16)));
/// refinement_int!(BoundedAbsIsize<const B: usize>(isize, |x| x >= -(B as isize) && x <= (B as isize)));
/// ```
#[macro_export]
macro_rules! refinement_int {
    ($(#$attr:tt)* $bounded_t:ident$(<$(const $cst_name:ident : $cst_ty:ty),*$(,)?>)?($t: ident, $($bytes:literal,)? |$x:ident| $body:expr)$(,)?) => {
        $crate::mk_bounded!($(#$attr)* $bounded_t<$($(const $cst_name:$cst_ty),*)?>($t $($bytes)?, |$x| $body));
    };
}

#[hax_lib::exclude]
const _: () = {
    impl<const MIN: usize, const MAX: usize, T> core::ops::Index<BoundedUsize<MIN, MAX>> for [T] {
        type Output = T;
        #[inline(always)]
        fn index(&self, index: BoundedUsize<MIN, MAX>) -> &Self::Output {
            &self[index.get()]
        }
    }

    impl<const MIN: usize, const MAX: usize, T> core::ops::IndexMut<BoundedUsize<MIN, MAX>> for [T] {
        #[inline(always)]
        fn index_mut(&mut self, index: BoundedUsize<MIN, MAX>) -> &mut Self::Output {
            &mut self[index.get()]
        }
    }
};

#[test]
fn tests() {
    refinement_int!(
        Test<const B: usize>(i16, 2, |x| B < 32768 && x >= -(B as i16) && x <= (B as i16))
    );

    use hax_lib::*;

    let mut zzz: Test<123> = (-122).into_checked();
    zzz += 32;

    let x: BoundedU8<0, 5> = 2.into_checked();
    let y: BoundedU8<5, 10> = (x + x).into_checked();

    let _ = x >> 3;
    let _ = x >> BoundedU8::<0, 5>::new(3);

    let _ = x / y;
    let _ = x * y;
    let _ = x + y;
    let _ = y - x;

    let _ = x / 1;
    let _ = x * 1;
    let _ = x + 1;
    let _ = x - 1;
    let _ = 4 / y;
    let _ = 4 * y;
    let _ = 4 + y;
    let _ = 4 - y;
}

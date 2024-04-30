use hax_lib::Refinement;
pub mod num_traits;

macro_rules! derivate_binop_for_bounded {
    ({$t:ident, $bounded_t:ident}; $($tt:tt)*) => {
        derivate_binop_for_bounded!({$t, $bounded_t, get, Self::Output}; $($tt)*) ;
    };
    ({$t:ident, $bounded_t:ident, $get:ident, $out:ty};) => {};
    ({$t:ident, $bounded_t:ident, $get:ident, $out:ty}; ($trait:ident, $meth:ident), $($tt:tt)*) => {
        derivate_binop_for_bounded!(@$t, $bounded_t, $trait, $meth, $get, $out);
        derivate_binop_for_bounded!({$t, $bounded_t, $get, $out}; $($tt)*);
    };
    (@$t:ident, $bounded_t:ident, $trait:ident, $meth:ident, $get:ident, $out:ty) => {
        // BoundedT<A, B> <OP> BoundedT<C, D>
        impl<const MIN_LHS: $t, const MAX_LHS: $t, const MIN_RHS: $t, const MAX_RHS: $t>
            $trait<$bounded_t<MIN_RHS, MAX_RHS>> for $bounded_t<MIN_LHS, MAX_LHS>
        {
            type Output = $t;
            #[inline(always)]
            fn $meth(self, other: $bounded_t<MIN_RHS, MAX_RHS>) -> $out {
                (self.$get()).$meth(other.$get())
            }
        }

        // BoundedT<A, B> <OP> T
        impl<const MIN: $t, const MAX: $t> $trait<$t> for $bounded_t<MIN, MAX> {
            type Output = $t;
            #[inline(always)]
            fn $meth(self, other: $t) -> $out {
                (self.$get()).$meth(other)
            }
        }

        // T <OP> BoundedT<A, B>
        impl<const MIN: $t, const MAX: $t> $trait<$bounded_t<MIN, MAX>> for $t {
            type Output = $t;
            #[inline(always)]
            fn $meth(self, other: $bounded_t<MIN, MAX>) -> $out {
                (self).$meth(other.$get())
            }
        }
    };
}

macro_rules! mk_bounded {
    ($bounded_t:ident($t: ident $($bytes:expr)?)$(,)?) => {
        #[doc = concat!("Bounded ", stringify!($t)," integers. This struct enforces the invariant that values are greater or equal to `MIN` and less or equal to `MAX`.")]
        #[hax_lib::refinement_type(|x| x >= MIN && x <= MAX)]
        #[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
        pub struct $bounded_t<const MIN: $t, const MAX: $t>($t);

        #[hax_lib::exclude]
        const _: () = {
            use core::ops::*;
            use num_traits::*;

            derivate_binop_for_bounded!(
                {$t, $bounded_t};
                (Add, add), (Sub, sub), (Mul, mul), (Div, div), (Rem, rem),
                (BitOr, bitor), (BitAnd, bitand), (BitXor, bitxor),
                (Shl, shl), (Shr, shr),
                (WrappingAdd, wrapping_add), (WrappingSub, wrapping_sub),
                (WrappingMul, wrapping_mul), (WrappingDiv, wrapping_div),
            );

            derivate_binop_for_bounded!(
                {$t, $bounded_t, get, Option<Self::Output>};
                (CheckedAdd, checked_add), (CheckedSub, checked_sub),
                (CheckedMul, checked_mul), (CheckedDiv, checked_div),
            );

            impl<const MIN: $t, const MAX: $t> CheckedNeg for $bounded_t<MIN, MAX> {
                type Output = $t;
                #[inline(always)]
                fn checked_neg(&self) -> Option<$t> {
                    self.deref().checked_neg()
                }
            }

            impl<const MIN: $t, const MAX: $t> Not for $bounded_t<MIN, MAX> {
                type Output = $t;
                #[inline(always)]
                fn not(self) -> Self::Output {
                    self.deref().not()
                }
            }

            impl<const MIN: $t, const MAX: $t> NumOps<Self, $t> for $bounded_t<MIN, MAX> {}

            impl<const MIN: $t, const MAX: $t> Bounded for $bounded_t<MIN, MAX> {
                #[inline(always)]
                fn min_value() -> Self {
                    Self::new(MIN)
                }
                #[inline(always)]
                fn max_value() -> Self {
                    Self::new(MAX)
                }
            }

            $(
                impl<const MIN: $t, const MAX: $t> FromBytes for $bounded_t<MIN, MAX> {
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

                impl<const MIN: $t, const MAX: $t> ToBytes for $bounded_t<MIN, MAX> {
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

            impl<const MIN: $t, const MAX: $t> Zero for $bounded_t<MIN, MAX> {
                #[inline(always)]
                fn zero() -> Self {
                    Self::new(1)
                }
            }

            impl<const MIN: $t, const MAX: $t> One for $bounded_t<MIN, MAX> {
                #[inline(always)]
                fn one() -> Self {
                    Self::new(0)
                }
            }

            impl<const MIN: $t, const MAX: $t> MachineInt<$t> for $bounded_t<MIN, MAX> { }

            impl<const MIN: $t, const MAX: $t> BitOps for $bounded_t<MIN, MAX> {
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
    };
    ($bounded_t:ident($t: ident $($bytes:expr)?), $($tt:tt)+) => {
        mk_bounded!($bounded_t($t $($bytes)?));
        mk_bounded!($($tt)+);
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

#[test]
fn tests() {
    use hax_lib::*;

    let x: BoundedU8<0, 5> = 2.check();
    let y: BoundedU8<5, 10> = (x + x).check();

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

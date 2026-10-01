use super::result::Result;

/// See [`std::convert::TryInto`]
#[hax_lib::attributes]
trait TryInto<T> {
    type Error;
    /// See [`std::convert::TryInto::try_into`]
    #[hax_lib::requires(true)]
    fn try_into(self) -> Result<T, Self::Error>;
}

/// See [`std::convert::Into`]
#[hax_lib::attributes]
pub trait Into<T> {
    /// See [`std::convert::Into::into`]
    #[hax_lib::requires(true)]
    fn into(self) -> T;
}

/// See [`std::convert::From`]
#[hax_lib::attributes]
pub trait From<T> {
    /// See [`std::convert::From::from`]
    #[hax_lib::requires(true)]
    fn from(x: T) -> Self;
}

/// See [`std::convert::TryFrom`]
#[hax_lib::attributes]
pub trait TryFrom<T>: Sized {
    type Error;
    /// See [`std::convert::TryFrom::try_from`]
    #[hax_lib::requires(true)]
    fn try_from(x: T) -> Result<Self, Self::Error>;
}

impl<T, U: From<T>> Into<U> for T {
    fn into(self) -> U {
        U::from(self)
    }
}

/// See [`std::convert::Infallible`]
pub struct Infallible;

/// See [`std::fmt::Debug`] for [`Infallible`]
#[cfg(not(hax_backend_fstar))]
impl crate::fmt::Debug for Infallible {
    fn fmt(&self, f: &mut crate::fmt::Formatter) -> crate::fmt::Result {
        crate::fmt::Result::Ok(())
    }
}

impl<T, U: From<T>> TryFrom<T> for U {
    type Error = Infallible;
    fn try_from(x: T) -> Result<Self, Self::Error> {
        Result::Ok(U::from(x))
    }
}

use crate::array::TryFromSliceError;
#[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
impl<T: Copy, const N: usize> TryFrom<&[T]> for [T; N] {
    type Error = TryFromSliceError;
    fn try_from(x: &[T]) -> Result<[T; N], TryFromSliceError> {
        if rust_primitives::slice::slice_length(x) == N {
            Result::Ok(rust_primitives::slice::array_from_fn(|i| {
                *rust_primitives::slice::slice_index(x, i)
            }))
        } else {
            Result::Err(TryFromSliceError)
        }
    }
}

impl<T, U: TryFrom<T>> TryInto<U> for T {
    type Error = U::Error;
    fn try_into(self) -> Result<U, Self::Error> {
        U::try_from(self)
    }
}

impl<T> From<T> for T {
    fn from(x: T) -> Self {
        x
    }
}

/// See [`std::convert::AsRef`]
#[hax_lib::attributes]
pub trait AsRef<T: ?Sized> {
    /// See [`std::convert::AsRef::as_ref`]
    #[hax_lib::requires(true)]
    fn as_ref(&self) -> &T;
}

// The blanket `AsRef<T> for T` can't cover the unsized `[T]`, so we provide the
// concrete slice impl.
impl<T> AsRef<[T]> for [T] {
    fn as_ref(&self) -> &[T] {
        self
    }
}

macro_rules! int_from {
    (
        $($From_t: ident)*,
        $($To_t: ident)*,
    ) => {
        $(
            #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
            impl From<$From_t> for $To_t {
                fn from(x: $From_t) -> $To_t {
                    x as $To_t
                }
            }
        )*
    }
}

use super::num::error::TryFromIntError;

// Bounds go through `crate::num::$To_t` rather than `$To_t` (real `core`); this
// avoids cyclic module dependencies in F*.
macro_rules! int_try_from {
    (
        $($From_t: ident)*,
        $($To_t: ident)*,
    ) => {
        $(
            #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
            impl TryFrom<$From_t> for $To_t {
                type Error = TryFromIntError;
                fn try_from(x: $From_t) -> Result<$To_t, TryFromIntError> {
                    if x > (crate::num::$To_t::MAX as $From_t) || x < (crate::num::$To_t::MIN as $From_t) {
                        Result::Err(TryFromIntError(()))
                    } else {
                        Result::Ok(x as $To_t)
                    }
                }
            }
        )*
    }
}

macro_rules! int_try_from_trivial {
    (
        $($From_t: ident)*,
        $($To_t: ident)*,
    ) => {
        $(
            #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
            impl TryFrom<$From_t> for $To_t {
                type Error = TryFromIntError;
                fn try_from(x: $From_t) -> Result<$To_t, TryFromIntError> {
                    Result::Ok(x as $To_t)
                }
            }
        )*
    }
}

int_from! {
    u8  u8  u16 u8  u16 u32 u8   u16  u32  u64  u8    u16,
    u16 u32 u32 u64 u64 u64 u128 u128 u128 u128 usize usize,
}

int_from! {
    i8  i8  i16 i8  i16 i32 i8   i16  i32  i64  i8    i16,
    i16 i32 i32 i64 i64 i64 i128 i128 i128 i128 isize isize,
}

int_from! {
    u8  u8  u8  u8   u8    u16 u16 u16  u32 u32  u64,
    i16 i32 i64 i128 isize i32 i64 i128 i64 i128 i128,
}

int_try_from! {
    u16 u32 u32 u64 u64 u64 u64   u128 u128 u128 u128 u128  usize usize usize usize,
    u8  u8  u16 u8  u16 u32 usize u8   u16  u32  u64  usize u8    u16   u32   u64,
}

int_try_from! {
    i16 i32 i32 i64 i64 i64 i64   i128 i128 i128 i128 i128  isize isize isize isize,
    i8  i8  i16 i8  i16 i32 isize i8   i16  i32  i64  isize i8    i16   i32   i64,
}

// We assume a 64-bits machine
int_try_from_trivial! {
    i32   isize u32   usize,
    isize i128  usize u128,
}

macro_rules! int_try_from_u_to_i {
    (
        $($From_t: ident)*,
        $($To_t: ident)*,
    ) => {
        $(
            #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
            impl TryFrom<$From_t> for $To_t {
                type Error = TryFromIntError;
                fn try_from(x: $From_t) -> Result<$To_t, TryFromIntError> {
                    if x > (crate::num::$To_t::MAX as $From_t) {
                        Result::Err(TryFromIntError(()))
                    } else {
                        Result::Ok(x as $To_t)
                    }
                }
            }
        )*
    }
}

macro_rules! int_try_from_i_to_u {
    (
        $($From_t: ident)*,
        $($To_t: ident)*,
    ) => {
        $(
            #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
            impl TryFrom<$From_t> for $To_t {
                type Error = TryFromIntError;
                #[allow(unused_comparisons)]
                fn try_from(x: $From_t) -> Result<$To_t, TryFromIntError> {
                    if x < 0 || (x as u128) > (crate::num::$To_t::MAX as u128) {
                        Result::Err(TryFromIntError(()))
                    } else {
                        Result::Ok(x as $To_t)
                    }
                }
            }
        )*
    }
}

int_try_from_u_to_i! {
    u8   u16 u16 u32 u32 u32 u64 u64 u64 u64  u128 u128 u128 u128 u128  usize usize usize usize usize,
    i8   i8  i16 i8  i16 i32 i8  i16 i32 i64  i8   i16  i32  i64  i128  i8    i16   i32   i64   isize,
}

int_try_from_i_to_u! {
    i8  i8  i8  i8  i8   i8    i16 i16 i16 i16 i16  i16   i32 i32 i32 i32 i32  i32   i64 i64 i64 i64 i64  i64   i128 i128 i128 i128 i128 i128  isize isize isize isize isize isize,
    u8  u16 u32 u64 u128 usize u8  u16 u32 u64 u128 usize u8  u16 u32 u64 u128 usize u8  u16 u32 u64 u128 usize u8   u16  u32  u64  u128 usize u8    u16   u32   u64   u128  usize,
}

// `From<bool>` for every integer type, which real `core` provides in
// `convert::num` (`false` maps to 0, `true` to 1). Appended at the end of the
// module: hax's F* disambiguator numbers the module's impls top-to-bottom, so
// new impls at the end leave the published `Core_models.Convert.impl_NN` names
// of every `From`/`TryFrom` instance above untouched.
macro_rules! int_from_bool {
    ($($To_t: ident)*) => {
        $(
            #[cfg_attr(hax_backend_legacy_lean, hax_lib::exclude)]
            impl From<core::primitive::bool> for $To_t {
                fn from(x: core::primitive::bool) -> $To_t {
                    if x { 1 } else { 0 }
                }
            }
        )*
    }
}

int_from_bool! { u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize }

#[cfg(test)]
mod tests {
    use crate::testing::Inject;
    use pastey::paste;
    use proptest::prelude::*;

    /// `Debug` for `Infallible` renders nothing, like every other `Debug` in
    /// the model.
    #[cfg(not(hax_backend_fstar))]
    #[test]
    fn test_infallible_debug() {
        let mut f = crate::fmt::Formatter;
        assert!(crate::fmt::Debug::fmt(&super::Infallible, &mut f).is_ok());
    }

    proptest! {
        #[test]
        fn test_from_identity(x in any::<u8>()) {
            prop_assert_eq!(<u8 as super::From<u8>>::from(x.inject()), x);
        }

        #[test]
        fn test_into_identity(x in any::<u8>()) {
            prop_assert_eq!(super::Into::<u8>::into(x.inject()), x);
        }

        // Model's `AsRef<[u8]>` vs std's, both projecting a slice to itself.
        #[test]
        fn test_as_ref_slice_identity(v in prop::collection::vec(any::<u8>(), 0..=8)) {
            let s: &[u8] = &v[..];
            prop_assert_eq!(
                super::AsRef::<[u8]>::as_ref(s),
                core::convert::AsRef::<[u8]>::as_ref(s)
            );
        }
    }

    macro_rules! from_bool_test {
        ($($To_t: ident)*) => {
            paste! {
                $(
                    proptest! {
                        #[test]
                        fn [<test_from_bool_to_ $To_t>](x in any::<bool>()) {
                            prop_assert_eq!(
                                <$To_t as super::From<bool>>::from(x),
                                <$To_t as core::convert::From<bool>>::from(x)
                            );
                        }
                    }
                )*
            }
        }
    }

    from_bool_test! { u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize }

    macro_rules! int_from_test {
            (
                $($From_t: ident)*,
                $($To_t: ident)*,
            ) => {
                paste!{
                    $(
                        proptest! {
                            #[test]
                            fn [<test_from_$From_t _to_ $To_t>](x in any::<$From_t>()) {
                                prop_assert_eq!(<$To_t as super::From<$From_t>>::from(x.inject()), x.into());
                            }
                        }
                    )*
                }
            }
        }

    macro_rules! int_try_from_test {
            (
                $($From_t: ident)*,
                $($To_t: ident)*,
            ) => {
                paste!{
                    $(
                        proptest!{
                            #[test]
                            fn [<test_try_from_$From_t _to_ $To_t>](x in any::<$From_t>()) {
                                prop_assert_eq!(
                                    <$To_t as super::TryFrom<$From_t>>::try_from(x.inject()),
                                    $To_t::try_from(x).inject()
                                );
                            }
                        }
                    )*
                }
            }
        }

    int_from_test! {
        u8  u8  u16 u8  u16 u32 u8   u16  u32  u64  u8    u16,
        u16 u32 u32 u64 u64 u64 u128 u128 u128 u128 usize usize,
    }

    int_from_test! {
        i8  i8  i16 i8  i16 i32 i8   i16  i32  i64  i8    i16,
        i16 i32 i32 i64 i64 i64 i128 i128 i128 i128 isize isize,
    }

    int_from_test! {
        u8  u8  u8  u8   u8    u16 u16 u16  u32 u32  u64,
        i16 i32 i64 i128 isize i32 i64 i128 i64 i128 i128,
    }

    int_try_from_test! {
        u16 u32 u32 u32   u64 u64 u64 u64   u128 u128 u128 u128 u128  usize usize usize usize usize,
        u8  u8  u16 usize u8  u16 u32 usize u8   u16  u32  u64  usize u8    u16   u32   u64   u128,
    }

    int_try_from_test! {
        i16 i32 i32 i32   i64 i64 i64 i64   i128 i128 i128 i128 i128  isize isize isize isize isize,
        i8  i8  i16 isize i8  i16 i32 isize i8   i16  i32  i64  isize i8    i16   i32   i64   i128,
    }

    int_try_from_test! {
        u8   u16 u16 u32 u32 u32 u64 u64 u64 u64  u128 u128 u128 u128 u128  usize usize usize usize usize,
        i8   i8  i16 i8  i16 i32 i8  i16 i32 i64  i8   i16  i32  i64  i128  i8    i16   i32   i64   isize,
    }

    int_try_from_test! {
        i8  i8  i8  i8  i8   i8    i16 i16 i16 i16 i16  i16   i32 i32 i32 i32 i32  i32   i64 i64 i64 i64 i64  i64   i128 i128 i128 i128 i128 i128  isize isize isize isize isize isize,
        u8  u16 u32 u64 u128 usize u8  u16 u32 u64 u128 usize u8  u16 u32 u64 u128 usize u8  u16 u32 u64 u128 usize u8   u16  u32  u64  u128 usize u8    u16   u32   u64   u128  usize,
    }

    proptest! {
        #[test]
        fn test_try_from_slice_to_array_success(arr in any::<[u8; 4]>()) {
            prop_assert_eq!(
                <[u8; 4] as super::TryFrom<&[u8]>>::try_from(arr.as_slice()).ok(),
                <[u8; 4] as core::convert::TryFrom<&[u8]>>::try_from(arr.as_slice()).ok().inject()
            );
        }

        #[test]
        fn test_try_into(x in any::<u32>()) {
            prop_assert_eq!(
                super::TryInto::<u8>::try_into(x.inject()),
                u8::try_from(x).inject()
            );
        }

        #[test]
        fn test_try_from_slice_to_array_length_mismatch(arr in any::<[u8; 3]>()) {
            prop_assert_eq!(
                <[u8; 4] as super::TryFrom<&[u8]>>::try_from(arr.as_slice()).ok(),
                <[u8; 4] as core::convert::TryFrom<&[u8]>>::try_from(arr.as_slice()).ok().inject()
            );
        }
    }
}

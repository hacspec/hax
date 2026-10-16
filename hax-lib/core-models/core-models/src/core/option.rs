/// See [`std::option::Option`]
#[cfg_attr(test, derive(PartialEq, Debug))]
pub enum Option<T> {
    /// See [`std::option::Option::Some`]
    Some(T),
    /// See [`std::option::Option::None`]
    None,
}

use self::Option::*;
use super::clone::Clone;
use super::default::Default;
use super::result::Result::*;
use super::result::*;
use rust_primitives::sequence::{Seq, seq_empty, seq_len, seq_one, seq_remove};
use rust_primitives::slice::{
    array_as_mut_slice, array_as_slice, array_from_mut, array_from_ref, slice_empty,
};

/// See [`std::fmt::Debug`] for [`Option`]
#[cfg(not(hax_backend_fstar))]
impl<T: crate::fmt::Debug> crate::fmt::Debug for Option<T> {
    fn fmt(&self, f: &mut crate::fmt::Formatter) -> crate::fmt::Result {
        match self {
            Some(x) => crate::fmt::Debug::fmt(x, f),
            None => crate::fmt::Result::Ok(()),
        }
    }
}

#[hax_lib::attributes]
impl<T> Option<T> {
    /// See [`std::option::Option::is_some`]
    #[hax_lib::ensures(|res| hax_lib::Prop::implies(res.into(), fstar!("Option_Some? self")))]
    pub fn is_some(&self) -> bool {
        matches!(*self, Some(_))
    }

    /// See [`std::option::Option::is_some_and`]
    pub fn is_some_and<F: FnOnce(T) -> bool>(self, f: F) -> bool {
        match self {
            None => false,
            Some(x) => f(x),
        }
    }

    /// See [`std::option::Option::is_none`]
    pub fn is_none(&self) -> bool {
        self.is_some() == false
    }

    /// See [`std::option::Option::is_none_or`]
    pub fn is_none_or<F: FnOnce(T) -> bool>(self, f: F) -> bool {
        match self {
            None => true,
            Some(x) => f(x),
        }
    }

    /// See [`std::option::Option::as_ref`]
    pub const fn as_ref(&self) -> Option<&T> {
        match *self {
            Some(ref x) => Some(x),
            None => None,
        }
    }

    /// See [`std::option::Option::as_mut`]
    // The `ref mut` binding trips hax's `&mut` restriction (HAX0003, hacspec/hax#420),
    // so this is excluded from the F* backend; aeneas/lean/native keep it.
    #[cfg(not(hax_backend_fstar))]
    pub fn as_mut(&mut self) -> Option<&mut T> {
        match *self {
            Some(ref mut x) => Some(x),
            None => None,
        }
    }

    /// See [`std::option::Option::expect`]
    #[cfg_attr(not(hax_backend_lean), hax_lib::requires(self.is_some()))]
    pub fn expect(self, _msg: &str) -> T {
        match self {
            Some(val) => val,
            None => super::panicking::internal::panic(),
        }
    }

    /// See [`std::option::Option::unwrap`]
    #[cfg_attr(not(hax_backend_lean), hax_lib::requires(self.is_some()))]
    pub fn unwrap(self) -> T {
        match self {
            Some(val) => val,
            None => super::panicking::internal::panic(),
        }
    }

    /// See [`std::option::Option::unwrap_or`]
    pub fn unwrap_or(self, default: T) -> T {
        match self {
            Some(x) => x,
            None => default,
        }
    }

    /// See [`std::option::Option::unwrap_or_else`]
    pub fn unwrap_or_else<F: FnOnce() -> T>(self, f: F) -> T {
        match self {
            Some(x) => x,
            None => f(),
        }
    }

    /// See [`std::option::Option::unwrap_or_default`]
    pub fn unwrap_or_default(self) -> T
    where
        T: Default,
    {
        match self {
            Some(x) => x,
            None => T::default(),
        }
    }

    /// See [`std::option::Option::map`]
    pub fn map<U, F>(self, f: F) -> Option<U>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Some(x) => Some(f(x)),
            None => None,
        }
    }

    /// See [`std::option::Option::map_or`]
    pub fn map_or<U, F>(self, default: U, f: F) -> U
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Some(t) => f(t),
            None => default,
        }
    }

    /// See [`std::option::Option::map_or_else`]
    pub fn map_or_else<U, D, F>(self, default: D, f: F) -> U
    where
        F: FnOnce(T) -> U,
        D: FnOnce() -> U,
    {
        match self {
            Some(t) => f(t),
            None => default(),
        }
    }

    /// See [`std::option::Option::map_or_default`]
    pub fn map_or_default<U, F>(self, f: F) -> U
    where
        F: FnOnce(T) -> U,
        U: Default,
    {
        match self {
            Some(t) => f(t),
            None => U::default(),
        }
    }

    /// See [`std::option::Option::ok_or`]
    pub fn ok_or<E>(self, err: E) -> Result<T, E> {
        match self {
            Some(v) => Ok(v),
            None => Err(err),
        }
    }

    /// See [`std::option::Option::ok_or_else`]
    pub fn ok_or_else<E, F: FnOnce() -> E>(self, err: F) -> Result<T, E> {
        match self {
            Some(v) => Ok(v),
            None => Err(err()),
        }
    }

    /// See [`std::option::Option::and_then`]
    pub fn and_then<U, F>(self, f: F) -> Option<U>
    where
        F: FnOnce(T) -> Option<U>,
    {
        match self {
            Some(x) => f(x),
            None => None,
        }
    }

    /// See [`std::option::Option::take`]
    ///
    /// Note: The interface in Rust is wrong, but is good after extraction.
    /// We cannot make a useful model with the right interface so we lose the executability.
    //
    // Excluded from Lean: the Lean side is the `FunsPrologue.lean` shim. The
    // tuple is also in hax's F* order, (new_self, returned), not aeneas's.
    #[cfg_attr(hax_backend_lean, hax_lib::exclude)]
    pub fn take(self) -> (Option<T>, Option<T>) {
        (None, self)
    }

    /// See [`std::option::Option::filter`]
    // opaque: F* cannot prove that the Fn output projection equals bool in an if-condition
    #[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
    pub fn filter<P: FnOnce(&T) -> bool>(self, predicate: P) -> Option<T> {
        match self {
            Some(x) => {
                if predicate(&x) {
                    Some(x)
                } else {
                    None
                }
            }
            None => None,
        }
    }

    /// See [`std::option::Option::or`]
    pub fn or(self, optb: Option<T>) -> Option<T> {
        match self {
            Some(x) => Some(x),
            None => optb,
        }
    }

    /// See [`std::option::Option::or_else`]
    pub fn or_else<F: FnOnce() -> Option<T>>(self, f: F) -> Option<T> {
        match self {
            Some(x) => Some(x),
            None => f(),
        }
    }

    /// See [`std::option::Option::xor`]
    pub fn xor(self, optb: Option<T>) -> Option<T> {
        match (self, optb) {
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            _ => None,
        }
    }

    /// See [`std::option::Option::zip`]
    pub fn zip<U>(self, other: Option<U>) -> Option<(T, U)> {
        match (self, other) {
            (Some(a), Some(b)) => Some((a, b)),
            _ => None,
        }
    }

    /// See [`std::option::Option::inspect`]
    pub fn inspect<F: FnOnce(&T)>(self, f: F) -> Option<T> {
        if let Some(ref x) = self {
            f(x);
        }
        self
    }

    /// See [`std::option::Option::and`]
    pub fn and<U>(self, optb: Option<U>) -> Option<U> {
        match self {
            Some(_) => optb,
            None => None,
        }
    }

    /// See [`std::option::Option::as_slice`]
    pub fn as_slice(&self) -> &[T] {
        match self {
            Some(x) => array_as_slice(array_from_ref(x)),
            None => slice_empty(),
        }
    }

    /// See [`std::option::Option::as_mut_slice`]
    // Excluded from F*, which cannot express the `&mut` return; opaque for Lean, as
    // aeneas cannot translate the `&mut []` borrow of a constant.
    #[cfg_attr(hax_backend_fstar, hax_lib::exclude)]
    #[cfg_attr(hax_backend_lean, hax_lib::opaque)]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        match self {
            Some(x) => array_as_mut_slice(array_from_mut(x)),
            None => &mut [],
        }
    }

    /// See [`std::option::Option::unwrap_unchecked`]
    // F*-only: aeneas crashes on a `requires` on an `unsafe fn` in a generic impl.
    #[cfg_attr(hax_backend_fstar, hax_lib::requires(self.is_some()))]
    pub unsafe fn unwrap_unchecked(self) -> T {
        match self {
            Some(x) => x,
            None => super::panicking::internal::panic(),
        }
    }

    /// See [`std::option::Option::iter`]
    pub fn iter(&self) -> Iter<'_, T> {
        match self {
            Some(x) => Iter(seq_one(x)),
            None => Iter(seq_empty()),
        }
    }

    /// See [`std::option::Option::zip_with`]
    pub fn zip_with<U, F, R>(self, other: Option<U>, f: F) -> Option<R>
    where
        F: FnOnce(T, U) -> R,
    {
        match (self, other) {
            (Some(a), Some(b)) => Some(f(a, b)),
            _ => None,
        }
    }

    /// See [`std::option::Option::reduce`]
    pub fn reduce<U, R, F>(self, other: Option<U>, f: F) -> Option<R>
    where
        T: crate::convert::Into<R>,
        U: crate::convert::Into<R>,
        F: FnOnce(T, U) -> R,
    {
        match (self, other) {
            (Some(a), Some(b)) => Some(f(a, b)),
            (Some(a), None) => Some(crate::convert::Into::into(a)),
            (None, Some(b)) => Some(crate::convert::Into::into(b)),
            (None, None) => None,
        }
    }

    /// See [`std::option::Option::as_deref`]
    pub fn as_deref(&self) -> Option<&T::Target>
    where
        T: crate::ops::deref::Deref,
    {
        match self {
            Some(t) => Some(crate::ops::deref::Deref::deref(t)),
            None => None,
        }
    }

    /// See [`std::option::Option::as_deref_mut`]
    // `DerefMut` is not modeled in F*.
    #[cfg(not(hax_backend_fstar))]
    pub fn as_deref_mut(&mut self) -> Option<&mut T::Target>
    where
        T: crate::ops::deref::DerefMut,
    {
        match self {
            Some(t) => Some(crate::ops::deref::DerefMut::deref_mut(t)),
            None => None,
        }
    }
}

// hax names inherent methods `impl_N__*` by impl position, so these match real
// core's; empty impls carry `hax_lib::attributes` so rustc keeps that order.

#[hax_lib::attributes]
impl<T, U> Option<(T, U)> {
    /// See [`std::option::Option::unzip`]
    pub fn unzip(self) -> (Option<T>, Option<U>) {
        match self {
            Some((a, b)) => (Some(a), Some(b)),
            None => (None, None),
        }
    }
}

// Anonymous lifetime: hax builds the impl's name from it, which must match real core's.
#[hax_lib::attributes]
impl<T> Option<&'_ T> {
    /// See [`std::option::Option::copied`]
    // `Copy` is `core`'s: `*x` needs a real copy.
    pub fn copied(self) -> Option<T>
    where
        T: Copy,
    {
        match self {
            Some(x) => Some(*x),
            None => None,
        }
    }

    /// See [`std::option::Option::cloned`]
    pub fn cloned(self) -> Option<T>
    where
        T: Clone,
    {
        match self {
            Some(x) => Some(x.clone()),
            None => None,
        }
    }
}

// Real core's `impl<T> Option<&mut T>` (`copied`/`cloned` on `&mut`).
#[hax_lib::attributes]
impl<T> Option<&'_ mut T> {}

#[hax_lib::attributes]
impl<T, E> Option<Result<T, E>> {
    /// See [`std::option::Option::transpose`]
    pub fn transpose(self) -> Result<Option<T>, E> {
        match self {
            Some(Ok(x)) => Ok(Some(x)),
            Some(Err(e)) => Err(e),
            None => Ok(None),
        }
    }
}

#[hax_lib::attributes]
impl<T> Default for Option<T> {
    /// See [`std::default::Default`]
    fn default() -> Option<T> {
        None
    }
}

#[cfg(not(hax_backend_fstar))]
#[hax_lib::attributes]
impl<T: super::clone::Clone> super::clone::Clone for Option<T> {
    fn clone(&self) -> Self {
        match self {
            Self::Some(arg0) => Self::Some(arg0.clone()),
            Self::None => Self::None,
        }
    }
}

#[hax_lib::attributes]
impl<T: super::cmp::PartialEq<T>> super::cmp::PartialEq<Option<T>> for Option<T> {
    #[cfg(not(hax_backend_fstar))]
    fn ne(&self, other: &Self) -> bool {
        self.eq(other) == false
    }
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Some(a), Self::Some(b)) => a.eq(b),
            (Self::None, Self::None) => true,
            _ => false,
        }
    }
}

// The `?` operator on `Option`, mirroring the `Try`/`FromResidual` impls on
// `Result`: `branch` sends `Some(v)` to `Continue(v)` and `None` to
// `Break(None)`; `from_residual` rebuilds `None` at the target type.
#[hax_lib::attributes]
impl<T> crate::ops::try_trait::Try for Option<T> {
    type Output = T;
    type Residual = Option<crate::convert::Infallible>;

    fn from_output(output: Self::Output) -> Self {
        Some(output)
    }

    fn branch(self) -> crate::ops::control_flow::ControlFlow<Self::Residual, Self::Output> {
        match self {
            Some(v) => crate::ops::control_flow::ControlFlow::Continue(v),
            None => crate::ops::control_flow::ControlFlow::Break(None),
        }
    }
}

/// The `None` half of `?` on `Option`: rebuild `None` at the target type. The
/// residual carries `Infallible`, so the `Some` arm is unreachable.
// opaque for F*: can't prove the `Some(_)` (`Infallible`) arm unreachable.
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
impl<T> crate::ops::try_trait::FromResidual<Option<crate::convert::Infallible>> for Option<T> {
    // Excluded from coverage: the `Some(_)` arm holds an `Infallible`, so no
    // test can construct a value that reaches it.
    #[cfg_attr(coverage_nightly, coverage(off))]
    fn from_residual(residual: Option<crate::convert::Infallible>) -> Self {
        match residual {
            None => None,
            Some(_) => super::panicking::internal::panic(),
        }
    }
}

/// See [`std::option::Iter`]
pub struct Iter<'a, T>(pub Seq<&'a T>);

#[hax_lib::attributes]
// `A`, not `T`, as in core: Lean names the instance after it.
impl<'a, A> crate::iter::traits::iterator::Iterator for Iter<'a, A> {
    type Item = &'a A;
    fn next(&mut self) -> Option<&'a A> {
        if seq_len(&self.0) == 0 {
            None
        } else {
            Some(seq_remove(&mut self.0, 0))
        }
    }
}

// Stand-in for real core's `Iterator for IterMut`.
#[hax_lib::attributes]
impl<T> Option<T> {}

/// See [`std::option::IntoIter`]
pub struct IntoIter<T>(pub Seq<T>);

#[hax_lib::attributes]
impl<T> crate::iter::traits::iterator::Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        if seq_len(&self.0) == 0 {
            None
        } else {
            Some(seq_remove(&mut self.0, 0))
        }
    }
}

#[hax_lib::attributes]
impl<T> crate::iter::traits::collect::IntoIterator for Option<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    fn into_iter(self) -> IntoIter<T> {
        match self {
            Some(x) => IntoIter(seq_one(x)),
            None => IntoIter(seq_empty()),
        }
    }
}

// Stand-ins for the trait impls real core has before `Option<Option<T>>`.
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}
#[hax_lib::attributes]
impl<T> Option<T> {}

#[hax_lib::attributes]
impl<T> Option<Option<T>> {
    /// See [`std::option::Option::flatten`]
    pub fn flatten(self) -> Option<T> {
        match self {
            Some(inner) => inner,
            None => None,
        }
    }
}

// Not in the core hax builds against yet, so their position is not pinned.
#[hax_lib::attributes]
impl<'a, T> Option<&'a Option<T>> {
    /// See [`std::option::Option::flatten_ref`]
    pub fn flatten_ref(self) -> Option<&'a T> {
        match self {
            Some(inner) => inner.as_ref(),
            None => None,
        }
    }
}

#[hax_lib::attributes]
impl<'a, T> Option<&'a mut Option<T>> {
    /// See [`std::option::Option::flatten_mut`]
    // Built on `as_mut`, which is not modeled in F*.
    #[cfg(not(hax_backend_fstar))]
    pub fn flatten_mut(self) -> Option<&'a mut T> {
        match self {
            Some(inner) => inner.as_mut(),
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::iter::traits::iterator::Iterator as ModelIterator;
    use crate::testing::Inject;
    use proptest::prelude::*;

    /// A `DerefMut` target: the model has no `DerefMut` for `&mut T`.
    #[cfg(not(hax_backend_fstar))]
    struct Cell(u8);
    #[cfg(not(hax_backend_fstar))]
    impl crate::ops::deref::Deref for Cell {
        type Target = u8;
        fn deref(&self) -> &u8 {
            &self.0
        }
    }
    #[cfg(not(hax_backend_fstar))]
    impl crate::ops::deref::DerefMut for Cell {
        fn deref_mut(&mut self) -> &mut u8 {
            &mut self.0
        }
    }

    /// `Debug` for `Option` forwards to the payload's.
    #[cfg(not(hax_backend_fstar))]
    #[test]
    fn test_option_debug() {
        use crate::testing::DebugWitness;
        let mut f = crate::fmt::Formatter;
        let ok = super::Some(DebugWitness { fails: false });
        let err = super::Some(DebugWitness { fails: true });
        assert!(crate::fmt::Debug::fmt(&ok, &mut f).is_ok());
        assert!(crate::fmt::Debug::fmt(&err, &mut f).is_err());
        assert!(crate::fmt::Debug::fmt(&super::Option::<DebugWitness>::None, &mut f).is_ok());
    }

    // `as_mut` is `cfg(not(hax_backend_fstar))` (F* cannot model a `&mut`
    // return), so its test has to carry the same gate.
    #[cfg(not(hax_backend_fstar))]
    proptest! {
        #[test]
        fn test_as_mut(x in any::<Option<u8>>()) {
            let mut model = x.clone().inject();
            let mut std_ = x;
            match (super::Option::as_mut(&mut model), std_.as_mut()) {
                (super::Option::Some(a), Some(b)) => prop_assert_eq!(*a, *b),
                (super::Option::None, None) => {}
                _ => prop_assert!(false, "as_mut disagreed with core"),
            }
        }
    }

    fn drain<I: ModelIterator>(mut it: I) -> Vec<I::Item> {
        let mut out = Vec::new();
        while let super::Option::Some(x) = it.next() {
            out.push(x);
        }
        out
    }

    proptest! {
        #[test]
        fn test_is_some(x in any::<Option<u8>>()) {
            prop_assert!(x.clone().inject().is_some() == x.is_some());
        }

        #[test]
        fn test_is_some_and(x in any::<Option<u8>>(), threshold in any::<u8>()) {
            let f = |v: u8| v > threshold;
            prop_assert!(x.clone().inject().is_some_and(f) == x.is_some_and(f));
        }

        #[test]
        fn test_is_none(x in any::<Option<u8>>()) {
            prop_assert!(x.clone().inject().is_none() == x.is_none());
        }

        #[test]
        fn test_is_none_or(x in any::<Option<u8>>(), threshold in any::<u8>()) {
            let f = |v: u8| v > threshold;
            prop_assert!(x.clone().inject().is_none_or(f) == x.is_none_or(f));
        }

        #[test]
        fn test_as_ref(x in any::<Option<u8>>()) {
            prop_assert!(x.clone().inject().as_ref().map(|v: &u8| *v) == x.as_ref().inject());
        }

        #[test]
        fn test_expect(x in any::<u8>()) {
            // Only test Some case since expect requires is_some()
            let opt = Some(x);
            prop_assert!(opt.clone().inject().expect("msg") == opt.expect("msg"));
        }

        #[test]
        fn test_unwrap(x in any::<u8>()) {
            // Only test Some case since unwrap requires is_some()
            let opt = Some(x);
            prop_assert!(opt.clone().inject().unwrap() == opt.unwrap());
        }

        #[test]
        fn test_unwrap_or(x in any::<Option<u8>>(), default in any::<u8>()) {
            prop_assert!(x.clone().inject().unwrap_or(default) == x.unwrap_or(default));
        }

        #[test]
        fn test_unwrap_or_else(x in any::<Option<u8>>(), default in any::<u8>()) {
            let f = || default;
            prop_assert!(x.clone().inject().unwrap_or_else(f) == x.unwrap_or_else(f));
        }

        #[test]
        fn test_unwrap_or_default(x in any::<Option<u8>>()) {
            prop_assert!(x.clone().inject().unwrap_or_default() == x.unwrap_or_default());
        }

        #[test]
        fn test_map(x in any::<Option<u8>>(), a in any::<[u8; 256]>()) {
            let f = |x: u8| a[x as usize];
            prop_assert!(x.clone().inject().map(f) == x.map(f).inject());
        }

        #[test]
        fn test_map_or(x in any::<Option<u8>>(), default in any::<u8>(), a in any::<[u8; 256]>()) {
            let f = |v: u8| a[v as usize];
            prop_assert!(x.clone().inject().map_or(default, f) == x.map_or(default, f));
        }

        #[test]
        fn test_map_or_else(x in any::<Option<u8>>(), default in any::<u8>(), a in any::<[u8; 256]>()) {
            let f = |v: u8| a[v as usize];
            let d = || default;
            prop_assert!(x.clone().inject().map_or_else(d, f) == x.map_or_else(d, f));
        }

        #[test]
        fn test_map_or_default(x in any::<Option<u8>>(), a in any::<[u8; 256]>()) {
            let f = |v: u8| a[v as usize];
            // map_or_default is unstable in std, so compare with equivalent behavior
            prop_assert!(x.clone().inject().map_or_default(f) == x.map(f).unwrap_or_default());
        }

        #[test]
        fn test_ok_or(x in any::<Option<u8>>(), err in any::<u8>()) {
            prop_assert!(x.clone().inject().ok_or(err) == x.ok_or(err).inject());
        }

        #[test]
        fn test_ok_or_else(x in any::<Option<u8>>(), err in any::<u8>()) {
            let f = || err;
            prop_assert!(x.clone().inject().ok_or_else(f) == x.ok_or_else(f).inject());
        }

        #[test]
        fn test_and_then(x in any::<Option<u8>>(), threshold in any::<u8>()) {
            let f_model = |v: u8| if v > threshold { super::Option::Some(v) } else { super::Option::None };
            let f_std = |v: u8| if v > threshold { Some(v) } else { None };
            prop_assert!(x.clone().inject().and_then(f_model) == x.and_then(f_std).inject());
        }

        #[test]
        fn test_filter(x in any::<Option<u8>>(), threshold in any::<u8>()) {
            let f = |v: &u8| *v > threshold;
            prop_assert!(x.clone().inject().filter(f) == x.filter(f).inject());
        }

        #[test]
        fn test_or(x in any::<Option<u8>>(), y in any::<Option<u8>>()) {
            prop_assert!(x.clone().inject().or(y.clone().inject()) == x.or(y).inject());
        }

        #[test]
        fn test_or_else(x in any::<Option<u8>>(), default in any::<u8>()) {
            let f_model = || super::Option::Some(default);
            let f_std = || Some(default);
            prop_assert!(x.clone().inject().or_else(f_model) == x.or_else(f_std).inject());
        }

        #[test]
        fn test_xor(x in any::<Option<u8>>(), y in any::<Option<u8>>()) {
            prop_assert!(x.clone().inject().xor(y.clone().inject()) == x.xor(y).inject());
        }

        #[test]
        fn test_zip(x in any::<Option<u8>>(), y in any::<Option<u8>>()) {
            let model_result = x.clone().inject().zip(y.clone().inject());
            let std_result = x.zip(y);
            prop_assert!(model_result == std_result.inject());
        }

        #[test]
        fn test_eq(x in any::<Option<u8>>(), y in any::<Option<u8>>()) {
            prop_assert_eq!(
                crate::cmp::PartialEq::eq(&x.clone().inject(), &y.clone().inject()),
                x == y
            );
        }

        // `f` runs only on `Some`, so the side effect is the observation.
        #[test]
        fn test_inspect(x in any::<Option<u8>>()) {
            let mut model_seen: Vec<u8> = Vec::new();
            let model_result = x.clone().inject().inspect(|v: &u8| model_seen.push(*v));
            let mut std_seen: Vec<u8> = Vec::new();
            let std_result = x.clone().inspect(|v| std_seen.push(*v));
            prop_assert!(model_result == std_result.inject());
            prop_assert_eq!(model_seen, std_seen);
        }

        #[test]
        fn test_flatten(x in any::<Option<Option<u8>>>()) {
            prop_assert!(x.inject().flatten() == x.flatten().inject());
        }

        #[test]
        fn test_take(x in any::<Option<u8>>()) {
            // std::option::Option::take takes &mut self and returns Option<T>,
            // leaving None in place. Our model returns (remaining, taken).
            let mut std_opt = x.clone();
            let taken_std = std_opt.take();
            let remaining_std = std_opt;

            let (remaining_model, taken_model) = x.inject().take();

            prop_assert!(remaining_model == remaining_std.inject());
            prop_assert!(taken_model == taken_std.inject());
        }

        #[test]
        fn test_and(x in any::<Option<u8>>(), y in any::<Option<u8>>()) {
            prop_assert!(x.clone().inject().and(y.clone().inject()) == x.and(y).inject());
        }

        #[test]
        fn test_as_slice(x in any::<Option<u8>>()) {
            let model = x.clone().inject();
            prop_assert_eq!(model.as_slice(), x.as_slice());
        }

        #[test]
        fn test_as_mut_slice(x in any::<Option<u8>>()) {
            let mut model = x.clone().inject();
            for r in model.as_mut_slice().iter_mut() {
                *r = r.wrapping_add(1);
            }
            let mut std_opt = x.clone();
            for r in std_opt.as_mut_slice().iter_mut() {
                *r = r.wrapping_add(1);
            }
            prop_assert!(model == std_opt.inject());
        }

        // Only `Some`: std's version is UB on `None`.

        #[test]
        fn test_unwrap_unchecked(v in any::<u8>()) {
            let opt = Some(v);
            prop_assert_eq!(
                unsafe { opt.clone().inject().unwrap_unchecked() },
                unsafe { opt.unwrap_unchecked() }
            );
        }

        #[test]
        fn test_unwrap_unchecked_on_none_panics(_ignored in any::<u8>()) {
            let panicked = std::panic::catch_unwind(|| unsafe {
                super::Option::<u8>::None.unwrap_unchecked()
            })
            .is_err();
            prop_assert!(panicked);
        }

        #[test]
        fn test_iter(x in any::<Option<u8>>()) {
            let model = x.clone().inject();
            prop_assert_eq!(
                drain(model.iter()).into_iter().copied().collect::<Vec<u8>>(),
                x.iter().copied().collect::<Vec<u8>>()
            );
        }

        #[test]
        fn test_into_iter(x in any::<Option<u8>>()) {
            use crate::iter::traits::collect::IntoIterator as ModelIntoIterator;
            let model = <super::Option<u8> as ModelIntoIterator>::into_iter(x.clone().inject());
            prop_assert_eq!(drain(model), x.into_iter().collect::<Vec<u8>>());
        }

        #[test]
        fn test_zip_with(x in any::<Option<u8>>(), y in any::<Option<u8>>()) {
            let f = |a: u8, b: u8| a.wrapping_add(b);
            prop_assert!(
                x.clone().inject().zip_with(y.clone().inject(), f)
                    == x.zip(y).map(|(a, b)| f(a, b)).inject()
            );
        }

        #[test]
        fn test_reduce(x in any::<Option<u8>>(), y in any::<Option<u8>>()) {
            let f = |a: u8, b: u8| a.wrapping_add(b);
            prop_assert!(x.clone().inject().reduce(y.clone().inject(), f) == x.reduce(y, f).inject());
        }

        #[test]
        fn test_unzip(x in any::<Option<(u8, u8)>>()) {
            let (a_model, b_model) = x.clone().inject().unzip();
            let (a_std, b_std) = x.unzip();
            prop_assert!(a_model == a_std.inject());
            prop_assert!(b_model == b_std.inject());
        }

        #[test]
        fn test_transpose(x in any::<Option<Result<u8, u8>>>()) {
            prop_assert!(x.clone().inject().transpose() == x.transpose().inject());
        }

        #[test]
        fn test_cloned(x in any::<Option<u8>>()) {
            let model: super::Option<&u8> = match &x {
                Some(v) => super::Some(v),
                None => super::None,
            };
            prop_assert!(model.cloned() == x.as_ref().cloned().inject());
        }

        #[test]
        fn test_copied(x in any::<Option<u8>>()) {
            let model: super::Option<&u8> = match &x {
                Some(v) => super::Some(v),
                None => super::None,
            };
            prop_assert!(model.copied() == x.as_ref().copied().inject());
        }

        #[test]
        fn test_as_deref(x in any::<Option<u8>>()) {
            let model: super::Option<&u8> = match &x {
                Some(v) => super::Some(v),
                None => super::None,
            };
            let std_opt: Option<&u8> = x.as_ref();
            prop_assert!(
                model.as_deref().map(|v: &u8| *v) == std_opt.as_deref().map(|v| *v).inject()
            );
        }

        #[test]
        fn test_as_deref_of_mut(x in any::<Option<u8>>()) {
            let mut y = x;
            let model: super::Option<&mut u8> = match &mut y {
                Some(v) => super::Some(v),
                None => super::None,
            };
            prop_assert!(model.as_deref().map(|v: &u8| *v) == x.inject());
        }

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_as_deref_mut(v in any::<u8>(), present in any::<bool>()) {
            let mut std_opt: Option<u8> = if present { Some(v) } else { None };
            let mut model: super::Option<Cell> = if present {
                super::Some(Cell(v))
            } else {
                super::None
            };
            if let Some(r) = std_opt.as_mut() {
                *r = r.wrapping_add(1);
            }
            prop_assert_eq!(*crate::ops::deref::Deref::deref(&Cell(v)), v);
            if let super::Some(r) = model.as_deref_mut() {
                *r = r.wrapping_add(1);
            }
            prop_assert_eq!(model.map(|c: Cell| c.0), std_opt.inject());
        }

        #[test]
        fn test_flatten_ref(inner in any::<Option<u8>>(), present in any::<bool>()) {
            let std_inner = inner.clone();
            let model_inner = inner.inject();
            let std_outer: Option<&Option<u8>> =
                if present { Some(&std_inner) } else { None };
            let model_outer: super::Option<&super::Option<u8>> = if present {
                super::Some(&model_inner)
            } else {
                super::None
            };
            prop_assert!(
                model_outer.flatten_ref().map(|v: &u8| *v)
                    == std_outer.and_then(|o| o.as_ref()).map(|v| *v).inject()
            );
        }

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_flatten_mut(inner in any::<Option<u8>>(), present in any::<bool>()) {
            let mut std_inner = inner.clone();
            let mut model_inner = inner.inject();
            {
                let std_outer: Option<&mut Option<u8>> =
                    if present { Some(&mut std_inner) } else { None };
                let model_outer: super::Option<&mut super::Option<u8>> = if present {
                    super::Some(&mut model_inner)
                } else {
                    super::None
                };
                if let Some(r) = std_outer.and_then(|o| o.as_mut()) {
                    *r = r.wrapping_add(1);
                }
                if let super::Some(r) = model_outer.flatten_mut() {
                    *r = r.wrapping_add(1);
                }
            }
            prop_assert!(model_inner == std_inner.inject());
        }

        #[test]
        fn test_option_eq(x in any::<Option<u8>>(), y in any::<Option<u8>>()) {
            prop_assert_eq!(
                <super::Option<u8> as crate::cmp::PartialEq<super::Option<u8>>>::eq(
                    &x.inject(), &y.inject()
                ),
                x == y
            );
        }

        // Small domain so equal pairs (the interesting case) come up often.
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_option_ne(x in prop::option::of(0u8..4), y in prop::option::of(0u8..4)) {
            prop_assert_eq!(
                <super::Option<u8> as crate::cmp::PartialEq<super::Option<u8>>>::ne(
                    &x.inject(), &y.inject()
                ),
                x != y
            );
        }

        #[test]
        fn test_try_branch(x in any::<Option<u8>>()) {
            use crate::ops::control_flow::ControlFlow;
            use crate::ops::try_trait::Try;
            match (x, Try::branch(x.inject())) {
                (Some(v), ControlFlow::Continue(w)) => prop_assert_eq!(v, w),
                (None, ControlFlow::Break(super::Option::None)) => {}
                _ => prop_assert!(false, "branch disagreed with the input"),
            }
        }

        // The two halves of `?` on `Option`: `from_output` wraps a value, and
        // `from_residual` rebuilds `None` at the target type.
        #[test]
        fn test_try_from_output_and_residual(x in any::<u8>()) {
            use crate::ops::try_trait::{FromResidual, Try};
            prop_assert!(matches!(
                <super::Option<u8> as Try>::from_output(x),
                super::Option::Some(v) if v == x
            ));
            let residual: super::Option<crate::convert::Infallible> = super::Option::None;
            prop_assert!(matches!(
                <super::Option<u8> as FromResidual<_>>::from_residual(residual),
                super::Option::None
            ));
        }

        // Under F*, `Clone` is a blanket impl and `Option` has none of its own.
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_option_clone(x in any::<Option<u8>>()) {
            prop_assert_eq!(
                <super::Option<u8> as crate::clone::Clone>::clone(&x.inject()),
                x.clone().inject()
            );
        }
    }

    #[test]
    fn test_option_default() {
        use crate::testing::Inject;
        let model: super::Option<u8> = <super::Option<u8> as crate::default::Default>::default();
        let std_default: Option<u8> = Default::default();
        assert_eq!(model, std_default.inject());
    }

    #[test]
    fn test_unwrap_on_none_panics() {
        crate::testing::panics_like_core(
            || super::Option::<u8>::None.unwrap(),
            || Option::<u8>::None.unwrap(),
        );
    }

    #[test]
    fn test_expect_on_none_panics() {
        crate::testing::panics_like_core(
            || super::Option::<u8>::None.expect("boom"),
            || Option::<u8>::None.expect("boom"),
        );
    }
}

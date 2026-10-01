/// See [`std::result::Result`]
#[cfg_attr(test, derive(PartialEq, Debug))]
pub enum Result<T, E> {
    /// See [`std::result::Result::Ok`]
    Ok(T),
    /// See [`std::result::Result::Err`]
    Err(E),
}

use self::Result::*;
use super::clone::Clone;
use super::default::Default;
use super::option::Option;
use rust_primitives::sequence::{Seq, seq_empty, seq_len, seq_one, seq_remove};

/// See [`std::fmt::Debug`] for [`Result`]
#[cfg(not(hax_backend_fstar))]
impl<T: super::fmt::Debug, E: super::fmt::Debug> super::fmt::Debug for Result<T, E> {
    fn fmt(&self, f: &mut super::fmt::Formatter) -> super::fmt::Result {
        match self {
            Result::Ok(x) => super::fmt::Debug::fmt(x, f),
            Result::Err(e) => super::fmt::Debug::fmt(e, f),
        }
    }
}

#[hax_lib::attributes]
impl<T, E> Result<T, E> {
    /// See [`std::result::Result::is_ok`]
    #[cfg_attr(hax_backend_lean, hax_lib::exclude)]
    pub fn is_ok(&self) -> bool {
        matches!(*self, Ok(_))
    }

    /// See [`std::result::Result::is_ok_and`]
    pub fn is_ok_and<F: FnOnce(T) -> bool>(self, f: F) -> bool {
        match self {
            Ok(t) => f(t),
            Err(_) => false,
        }
    }

    /// See [`std::result::Result::is_err`]
    #[cfg_attr(hax_backend_lean, hax_lib::exclude)]
    pub fn is_err(&self) -> bool {
        !self.is_ok()
    }

    /// See [`std::result::Result::is_err_and`]
    pub fn is_err_and<F: FnOnce(E) -> bool>(self, f: F) -> bool {
        match self {
            Ok(_) => false,
            Err(e) => f(e),
        }
    }

    /// See [`std::result::Result::as_ref`]
    #[cfg_attr(hax_backend_lean, hax_lib::exclude)]
    pub const fn as_ref(&self) -> Result<&T, &E> {
        match *self {
            Ok(ref t) => Ok(t),
            Err(ref e) => Err(e),
        }
    }

    /// See [`std::result::Result::as_mut`]
    #[hax_lib::exclude]
    pub fn as_mut(&mut self) -> Result<&mut T, &mut E> {
        match *self {
            Ok(ref mut t) => Ok(t),
            Err(ref mut e) => Err(e),
        }
    }

    /// See [`std::result::Result::expect`]
    #[cfg(hax_backend_fstar)]
    #[hax_lib::requires(self.is_ok())]
    pub fn expect(self, _msg: &str) -> T {
        match self {
            Ok(t) => t,
            Err(_) => super::panicking::internal::panic(),
        }
    }

    /// See [`std::result::Result::unwrap`]
    #[cfg(hax_backend_fstar)]
    #[hax_lib::requires(self.is_ok())]
    pub fn unwrap(self) -> T {
        match self {
            Ok(t) => t,
            Err(_) => super::panicking::internal::panic(),
        }
    }

    /// See [`std::result::Result::expect_err`]
    #[cfg(hax_backend_fstar)]
    #[hax_lib::requires(self.is_err())]
    pub fn expect_err(self, _msg: &str) -> E {
        match self {
            Ok(_) => super::panicking::internal::panic(),
            Err(e) => e,
        }
    }

    /// See [`std::result::Result::unwrap_err`]
    #[cfg(hax_backend_fstar)]
    #[hax_lib::requires(self.is_err())]
    pub fn unwrap_err(self) -> E {
        match self {
            Ok(_) => super::panicking::internal::panic(),
            Err(e) => e,
        }
    }

    /// See [`std::result::Result::unwrap_or_else`]
    pub fn unwrap_or_else<F: FnOnce(E) -> T>(self, op: F) -> T {
        match self {
            Ok(t) => t,
            Err(e) => op(e),
        }
    }

    /// See [`std::result::Result::unwrap_or_default`]
    pub fn unwrap_or_default(self) -> T
    where
        T: Default,
    {
        match self {
            Ok(t) => t,
            Err(_) => T::default(),
        }
    }

    /// See [`std::result::Result::map`]
    pub fn map<U, F>(self, op: F) -> Result<U, E>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Ok(t) => Ok(op(t)),
            Err(e) => Err(e),
        }
    }

    /// See [`std::result::Result::map_or`]
    pub fn map_or<U, F>(self, default: U, f: F) -> U
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Ok(t) => f(t),
            Err(_) => default,
        }
    }

    /// See [`std::result::Result::map_or_else`]
    pub fn map_or_else<U, D, F>(self, default: D, f: F) -> U
    where
        D: FnOnce(E) -> U,
        F: FnOnce(T) -> U,
    {
        match self {
            Ok(t) => f(t),
            Err(e) => default(e),
        }
    }

    /// See [`std::result::Result::map_or_default`]
    #[cfg_attr(hax_backend_lean, hax_lib::exclude)]
    pub fn map_or_default<U, F>(self, f: F) -> U
    where
        F: FnOnce(T) -> U,
        U: Default,
    {
        match self {
            Ok(t) => f(t),
            Err(_) => U::default(),
        }
    }

    /// See [`std::result::Result::inspect`]
    pub fn inspect<F: FnOnce(&T)>(self, f: F) -> Result<T, E> {
        if let Ok(ref t) = self {
            f(t);
        }
        self
    }

    /// See [`std::result::Result::inspect_err`]
    pub fn inspect_err<F: FnOnce(&E)>(self, f: F) -> Result<T, E> {
        if let Err(ref e) = self {
            f(e);
        }
        self
    }

    /// See [`std::result::Result::ok`]
    #[cfg_attr(hax_backend_lean, hax_lib::exclude)]
    pub fn ok(self) -> Option<T> {
        match self {
            Ok(x) => Option::Some(x),
            Err(_) => Option::None,
        }
    }

    /// See [`std::result::Result::err`]
    #[cfg_attr(hax_backend_lean, hax_lib::exclude)]
    pub fn err(self) -> Option<E> {
        match self {
            Ok(_) => Option::None,
            Err(e) => Option::Some(e),
        }
    }

    /// See [`std::result::Result::and`]
    pub fn and<U>(self, res: Result<U, E>) -> Result<U, E> {
        match self {
            Ok(_) => res,
            Err(e) => Err(e),
        }
    }

    /// See [`std::result::Result::and_then`]
    pub fn and_then<U, F>(self, op: F) -> Result<U, E>
    where
        F: FnOnce(T) -> Result<U, E>,
    {
        match self {
            Ok(t) => op(t),
            Err(e) => Err(e),
        }
    }

    /// See [`std::result::Result::or`]
    pub fn or<F>(self, res: Result<T, F>) -> Result<T, F> {
        match self {
            Ok(t) => Ok(t),
            Err(_) => res,
        }
    }

    /// See [`std::result::Result::or_else`]
    pub fn or_else<F, O: FnOnce(E) -> Result<T, F>>(self, op: O) -> Result<T, F> {
        match self {
            Ok(t) => Ok(t),
            Err(e) => op(e),
        }
    }

    /// See [`std::result::Result::unwrap_or`]
    pub fn unwrap_or(self, default: T) -> T {
        match self {
            Ok(t) => t,
            Err(_) => default,
        }
    }
    /// See [`std::result::Result::map_err`]
    pub fn map_err<F, O>(self, op: O) -> Result<T, F>
    where
        O: FnOnce(E) -> F,
    {
        match self {
            Ok(t) => Ok(t),
            Err(e) => Err(op(e)),
        }
    }

    /// See [`std::result::Result::unwrap_unchecked`]
    // F*-only: aeneas crashes on a `requires` on an `unsafe fn` in a generic impl.
    #[cfg_attr(hax_backend_fstar, hax_lib::requires(self.is_ok()))]
    pub unsafe fn unwrap_unchecked(self) -> T {
        match self {
            Ok(t) => t,
            Err(_) => super::panicking::internal::panic(),
        }
    }

    /// See [`std::result::Result::unwrap_err_unchecked`]
    #[cfg_attr(hax_backend_fstar, hax_lib::requires(self.is_err()))]
    pub unsafe fn unwrap_err_unchecked(self) -> E {
        match self {
            Ok(_) => super::panicking::internal::panic(),
            Err(e) => e,
        }
    }

    /// See [`std::result::Result::iter`]
    pub fn iter(&self) -> Iter<'_, T> {
        match self {
            Ok(t) => Iter(seq_one(t)),
            Err(_) => Iter(seq_empty()),
        }
    }

    /// See [`std::result::Result::as_deref`]
    pub fn as_deref(&self) -> Result<&T::Target, &E>
    where
        T: crate::ops::deref::Deref,
    {
        match self {
            Ok(t) => Ok(crate::ops::deref::Deref::deref(t)),
            Err(e) => Err(e),
        }
    }

    /// See [`std::result::Result::as_deref_mut`]
    // `DerefMut` is not modeled in F*.
    #[cfg(not(hax_backend_fstar))]
    pub fn as_deref_mut(&mut self) -> Result<&mut T::Target, &mut E>
    where
        T: crate::ops::deref::DerefMut,
    {
        match self {
            Ok(t) => Ok(crate::ops::deref::DerefMut::deref_mut(t)),
            Err(e) => Err(e),
        }
    }
}

/// aeneas/lean copies of the four methods whose std signature carries a `Debug`
/// bound: charon emits the dictionary, so the model must take it, but the F*
/// versions above must stay bound-free to keep their `impl__` names.
#[cfg(not(hax_backend_fstar))]
#[hax_lib::attributes]
impl<T, E> Result<T, E> {
    /// See [`std::result::Result::expect`]
    #[cfg_attr(not(hax_backend_lean), hax_lib::requires(self.is_ok()))]
    pub fn expect(self, _msg: &str) -> T
    where
        E: super::fmt::Debug,
    {
        match self {
            Ok(t) => t,
            Err(_) => super::panicking::internal::panic(),
        }
    }

    /// See [`std::result::Result::unwrap`]
    #[cfg_attr(not(hax_backend_lean), hax_lib::requires(self.is_ok()))]
    pub fn unwrap(self) -> T
    where
        E: super::fmt::Debug,
    {
        match self {
            Ok(t) => t,
            Err(_) => super::panicking::internal::panic(),
        }
    }

    /// See [`std::result::Result::expect_err`]
    #[cfg_attr(not(hax_backend_lean), hax_lib::requires(self.is_err()))]
    pub fn expect_err(self, _msg: &str) -> E
    where
        T: super::fmt::Debug,
    {
        match self {
            Ok(_) => super::panicking::internal::panic(),
            Err(e) => e,
        }
    }

    /// See [`std::result::Result::unwrap_err`]
    #[cfg_attr(not(hax_backend_lean), hax_lib::requires(self.is_err()))]
    pub fn unwrap_err(self) -> E
    where
        T: super::fmt::Debug,
    {
        match self {
            Ok(_) => super::panicking::internal::panic(),
            Err(e) => e,
        }
    }
}

// hax names inherent methods `impl_N__*` by impl position, so these match real
// core's; empty impls carry `hax_lib::attributes` so rustc keeps that order.

// Anonymous lifetime: see `Option<&'_ T>`. `Copy` is `core`'s: `*t` needs a real copy.
#[hax_lib::attributes]
impl<T, E> Result<&'_ T, E> {
    /// See [`std::result::Result::copied`]
    pub fn copied(self) -> Result<T, E>
    where
        T: Copy,
    {
        match self {
            Ok(t) => Ok(*t),
            Err(e) => Err(e),
        }
    }

    /// See [`std::result::Result::cloned`]
    pub fn cloned(self) -> Result<T, E>
    where
        T: Clone,
    {
        match self {
            Ok(t) => Ok(t.clone()),
            Err(e) => Err(e),
        }
    }
}

// Real core's `impl<T, E> Result<&mut T, E>` (`copied`/`cloned` on `&mut`).
#[hax_lib::attributes]
impl<T, E> Result<&'_ mut T, E> {}

#[cfg(hax_backend_fstar)]
#[hax_lib::attributes]
#[cfg_attr(hax_backend_lean, hax_lib::exclude)]
impl<T, E> Result<Option<T>, E> {
    /// See [`std::result::Result::transpose`]
    pub fn transpose(self) -> Option<Result<T, E>> {
        match self {
            Ok(Option::Some(t)) => Option::Some(Ok(t)),
            Ok(Option::None) => Option::None,
            Err(e) => Option::Some(Err(e)),
        }
    }
}

#[hax_lib::attributes]
#[cfg_attr(hax_backend_lean, hax_lib::exclude)]
impl<T, E> Result<Result<T, E>, E> {
    /// See [`std::result::Result::flatten`]
    pub fn flatten(self) -> Result<T, E> {
        match self {
            Ok(inner) => inner,
            Err(e) => Err(e),
        }
    }
}

/// Yields a `Seq` by value, for the `Result` shunt below: `V::from_iter` needs
/// an `IntoIterator<Item = A>`, and `slice::Iter` only yields references.
struct SeqIter<A>(rust_primitives::sequence::Seq<A>);

#[hax_lib::attributes]
impl<A> crate::iter::traits::iterator::Iterator for SeqIter<A> {
    type Item = A;

    fn next(&mut self) -> crate::option::Option<A> {
        if rust_primitives::sequence::seq_len(&self.0) == 0 {
            crate::option::Option::None
        } else {
            crate::option::Option::Some(rust_primitives::sequence::seq_remove(&mut self.0, 0))
        }
    }
}

/// See [`std::iter::FromIterator`] for `Result`: buffers the `Ok`s, stops at
/// the first `Err`. std threads a `&mut Option<E>` through `V::from_iter`,
/// which the model cannot, hence the `Seq`. `while` rather than an early
/// `return`, which hax cannot functionalize.
// F*: while-loop over `next`, as in the `iter_*` helpers.
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
// Lean: extracting this trips aeneas's `type_var_id` on `IntoIterator::Item`,
// as for `Vec`. Same fold hand-written in `FunsEpilogue.lean`.
#[cfg_attr(hax_backend_lean, hax_lib::exclude)]
#[hax_lib::attributes]
impl<A, E, V: crate::iter::traits::collect::FromIterator<A>>
    crate::iter::traits::collect::FromIterator<Result<A, E>> for Result<V, E>
{
    fn from_iter<T: crate::iter::traits::collect::IntoIterator<Item = Result<A, E>>>(
        iter: T,
    ) -> Result<V, E> {
        let mut it = crate::iter::traits::collect::IntoIterator::into_iter(iter);
        let mut acc = rust_primitives::sequence::seq_empty();
        let mut err: crate::option::Option<E> = crate::option::Option::None;
        let mut done = false;
        while !done {
            match crate::iter::traits::iterator::Iterator::next(&mut it) {
                crate::option::Option::None => done = true,
                crate::option::Option::Some(Ok(a)) => {
                    rust_primitives::sequence::seq_push(&mut acc, a)
                }
                crate::option::Option::Some(Err(e)) => {
                    err = crate::option::Option::Some(e);
                    done = true;
                }
            }
        }
        match err {
            crate::option::Option::Some(e) => Err(e),
            crate::option::Option::None => {
                Ok(<V as crate::iter::traits::collect::FromIterator<A>>::from_iter(SeqIter(acc)))
            }
        }
    }
}

#[hax_lib::attributes]
impl<T, E> crate::ops::try_trait::Try for Result<T, E> {
    type Output = T;
    type Residual = Result<crate::convert::Infallible, E>;

    #[inline]
    fn from_output(output: Self::Output) -> Self {
        Ok(output)
    }

    #[inline]
    fn branch(self) -> crate::ops::control_flow::ControlFlow<Self::Residual, Self::Output> {
        match self {
            Ok(v) => crate::ops::control_flow::ControlFlow::Continue(v),
            Err(e) => crate::ops::control_flow::ControlFlow::Break(Err(e)),
        }
    }
}

#[cfg(not(hax_backend_fstar))]
#[hax_lib::attributes]
impl<T, E> Result<Option<T>, E> {
    /// See [`std::result::Result::transpose`]
    pub fn transpose(self) -> Option<Result<T, E>> {
        match self {
            Ok(Option::Some(t)) => Option::Some(Ok(t)),
            Ok(Option::None) => Option::None,
            Err(e) => Option::Some(Err(e)),
        }
    }
}

/// F* compares `Result`s with its own structural equality, so this is only
/// extracted for aeneas/lean.
#[cfg(not(hax_backend_fstar))]
#[hax_lib::attributes]
impl<T: super::cmp::PartialEq<T>, E: super::cmp::PartialEq<E>> super::cmp::PartialEq<Result<T, E>>
    for Result<T, E>
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Ok(a), Ok(b)) => a.eq(b),
            (Err(a), Err(b)) => a.eq(b),
            _ => false,
        }
    }
}

/// The error half of `?`: re-inject the `Err(e)` residual, widening the error
/// via `From` (mirrors std's `impl<T, E, F: From<E>> ... for Result<T, F>`). `Ok`
/// is unreachable — the residual's payload is `Infallible`.
// opaque for F*: can't prove the `Ok(_)` arm (`Infallible`) unreachable.
#[cfg_attr(hax_backend_fstar, hax_lib::opaque)]
impl<T, E, F: crate::convert::From<E>>
    crate::ops::try_trait::FromResidual<Result<crate::convert::Infallible, E>> for Result<T, F>
{
    fn from_residual(residual: Result<crate::convert::Infallible, E>) -> Self {
        match residual {
            Err(e) => Err(<F as crate::convert::From<E>>::from(e)),
            Ok(_) => super::panicking::internal::panic(),
        }
    }
}

/// Mirrors the `Option` instance in `core/option.rs`.
#[cfg(not(hax_backend_fstar))]
#[hax_lib::attributes]
impl<T: super::clone::Clone, E: super::clone::Clone> super::clone::Clone for Result<T, E> {
    fn clone(&self) -> Self {
        match self {
            Ok(v) => Ok(super::clone::Clone::clone(v)),
            Err(e) => Err(super::clone::Clone::clone(e)),
        }
    }
}

/// See [`std::result::Iter`]
pub struct Iter<'a, T>(pub Seq<&'a T>);

#[hax_lib::attributes]
impl<'a, T> crate::iter::traits::iterator::Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<&'a T> {
        if seq_len(&self.0) == 0 {
            Option::None
        } else {
            Option::Some(seq_remove(&mut self.0, 0))
        }
    }
}

// Stand-in for real core's `Iterator for IterMut`.
#[hax_lib::attributes]
impl<T, E> Result<T, E> {}

/// See [`std::result::IntoIter`]
pub struct IntoIter<T>(pub Seq<T>);

#[hax_lib::attributes]
impl<T> crate::iter::traits::iterator::Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        if seq_len(&self.0) == 0 {
            Option::None
        } else {
            Option::Some(seq_remove(&mut self.0, 0))
        }
    }
}

#[hax_lib::attributes]
impl<T, E> crate::iter::traits::collect::IntoIterator for Result<T, E> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    fn into_iter(self) -> IntoIter<T> {
        match self {
            Ok(t) => IntoIter(seq_one(t)),
            Err(_) => IntoIter(seq_empty()),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::iter::traits::iterator::Iterator as ModelIterator;
    use crate::option::Option as ModelOption;
    #[cfg(not(hax_backend_fstar))]
    use crate::testing::CloneWitness;
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

    /// `Debug` for `Result` forwards to the payload's, on either side.
    #[cfg(not(hax_backend_fstar))]
    #[test]
    fn test_result_debug() {
        use crate::testing::DebugWitness;
        let mut f = crate::fmt::Formatter;
        for fails in [false, true] {
            // One instantiation for both arms, so coverage sees them together.
            let ok = super::Ok::<_, DebugWitness>(DebugWitness { fails });
            let err = super::Err::<DebugWitness, _>(DebugWitness { fails });
            assert_eq!(crate::fmt::Debug::fmt(&ok, &mut f).is_err(), fails);
            assert_eq!(crate::fmt::Debug::fmt(&err, &mut f).is_err(), fails);
        }
    }

    fn drain<I: ModelIterator>(mut it: I) -> Vec<I::Item> {
        let mut out = Vec::new();
        while let ModelOption::Some(x) = it.next() {
            out.push(x);
        }
        out
    }

    proptest! {
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_clone_applies_element_clone(v in any::<u8>()) {
            let ok: Result<CloneWitness, CloneWitness> = Ok(CloneWitness::new(v));
            prop_assert_eq!(
                crate::clone::Clone::clone(&ok.inject()),
                ok.clone().inject()
            );
            let err: Result<CloneWitness, CloneWitness> = Err(CloneWitness::new(v));
            prop_assert_eq!(
                crate::clone::Clone::clone(&err.inject()),
                err.clone().inject()
            );
        }

        #[test]
        fn test_is_ok(x in any::<Result<u8, u8>>()) {
            prop_assert!(x.clone().inject().is_ok() == x.is_ok());
        }

        #[test]
        fn test_is_ok_and(x in any::<Result<u8, u8>>(), threshold in any::<u8>()) {
            let f = |v: u8| v > threshold;
            prop_assert!(x.clone().inject().is_ok_and(f) == x.is_ok_and(f));
        }

        #[test]
        fn test_is_err(x in any::<Result<u8, u8>>()) {
            prop_assert!(x.clone().inject().is_err() == x.is_err());
        }

        #[test]
        fn test_is_err_and(x in any::<Result<u8, u8>>(), threshold in any::<u8>()) {
            let f = |e: u8| e > threshold;
            prop_assert!(x.clone().inject().is_err_and(f) == x.is_err_and(f));
        }

        #[test]
        fn test_as_ref(x in any::<Result<u8, u8>>()) {
            // Test that as_ref preserves the structure and allows access to the value
            let model = x.clone().inject();
            let model_ref = model.as_ref();
            prop_assert!(x.clone().inject().as_ref() == x.as_ref().inject().as_ref())
        }

        #[test]
        fn test_expect(v in any::<u8>()) {
            // Only test Ok case since expect requires is_ok()
            let res: Result<u8, u8> = Ok(v);
            prop_assert!(res.clone().inject().expect("msg") == res.expect("msg"));
        }

        #[test]
        fn test_unwrap(v in any::<u8>()) {
            // Only test Ok case since unwrap requires is_ok()
            let res: Result<u8, u8> = Ok(v);
            prop_assert!(res.clone().inject().unwrap() == res.unwrap());
        }

        #[test]
        fn test_expect_err(e in any::<u8>()) {
            // Only test Err case since expect_err requires is_err()
            let res: Result<u8, u8> = Err(e);
            prop_assert!(res.clone().inject().expect_err("msg") == res.expect_err("msg"));
        }

        #[test]
        fn test_unwrap_err(e in any::<u8>()) {
            // Only test Err case since unwrap_err requires is_err()
            let res: Result<u8, u8> = Err(e);
            prop_assert!(res.clone().inject().unwrap_err() == res.unwrap_err());
        }

        #[test]
        fn test_unwrap_or(x in any::<Result<u8, u8>>(), default in any::<u8>()) {
            prop_assert!(x.clone().inject().unwrap_or(default) == x.unwrap_or(default));
        }

        #[test]
        fn test_unwrap_or_else(x in any::<Result<u8, u8>>(), a in any::<[u8; 256]>()) {
            let f = |e: u8| a[e as usize];
            prop_assert!(x.clone().inject().unwrap_or_else(f) == x.unwrap_or_else(f));
        }

        #[test]
        fn test_unwrap_or_default(x in any::<Result<u8, u8>>()) {
            prop_assert!(x.clone().inject().unwrap_or_default() == x.unwrap_or_default());
        }

        #[test]
        fn test_map(x in any::<Result<u8, u8>>(), a in any::<[u8; 256]>()) {
            let f = |v: u8| a[v as usize];
            prop_assert!(x.clone().inject().map(f) == x.map(f).inject());
        }

        #[test]
        fn test_map_or(x in any::<Result<u8, u8>>(), default in any::<u8>(), a in any::<[u8; 256]>()) {
            let f = |v: u8| a[v as usize];
            prop_assert!(x.clone().inject().map_or(default, f) == x.map_or(default, f));
        }

        #[test]
        fn test_map_or_else(x in any::<Result<u8, u8>>(), a in any::<[u8; 256]>(), b in any::<[u8; 256]>()) {
            let f = |v: u8| a[v as usize];
            let d = |e: u8| b[e as usize];
            prop_assert!(x.clone().inject().map_or_else(d, f) == x.map_or_else(d, f));
        }

        #[test]
        fn test_map_or_default(x in any::<Result<u8, u8>>(), a in any::<[u8; 256]>()) {
            let f = |v: u8| a[v as usize];
            // map_or_default is unstable in std, so compare with equivalent behavior
            prop_assert!(x.clone().inject().map_or_default(f) == x.map(f).unwrap_or_default());
        }

        #[test]
        fn test_map_err(x in any::<Result<u8, u8>>(), a in any::<[u8; 256]>()) {
            let f = |e: u8| a[e as usize];
            prop_assert!(x.clone().inject().map_err(f) == x.map_err(f).inject());
        }

        #[test]
        fn test_ok(x in any::<Result<u8, u8>>()) {
            prop_assert!(x.clone().inject().ok() == x.ok().inject());
        }

        #[test]
        fn test_err(x in any::<Result<u8, u8>>()) {
            prop_assert!(x.clone().inject().err() == x.err().inject());
        }

        #[test]
        fn test_and(x in any::<Result<u8, u8>>(), y in any::<Result<u8, u8>>()) {
            prop_assert!(x.clone().inject().and(y.clone().inject()) == x.and(y).inject());
        }

        #[test]
        fn test_and_then(x in any::<Result<u8, u8>>(), threshold in any::<u8>()) {
            let f_model = |v: u8| if v > threshold { super::Result::Ok(v) } else { super::Result::Err(v) };
            let f_std = |v: u8| if v > threshold { Ok(v) } else { Err(v) };
            prop_assert!(x.clone().inject().and_then(f_model) == x.and_then(f_std).inject());
        }

        #[test]
        fn test_or(x in any::<Result<u8, u8>>(), y in any::<Result<u8, u8>>()) {
            prop_assert!(x.clone().inject().or(y.clone().inject()) == x.or(y).inject());
        }

        #[test]
        fn test_or_else(x in any::<Result<u8, u8>>(), a in any::<[u8; 256]>()) {
            let f_model = |e: u8| super::Result::Ok::<u8, u8>(a[e as usize]);
            let f_std = |e: u8| Ok::<u8, u8>(a[e as usize]);
            prop_assert!(x.clone().inject().or_else(f_model) == x.or_else(f_std).inject());
        }

        #[test]
        fn test_cloned(x in any::<Result<u8, u8>>()) {
            let model: super::Result<&u8, u8> = match &x {
                Ok(t) => super::Result::Ok(t),
                Err(e) => super::Result::Err(*e),
            };
            prop_assert!(model.cloned() == x.inject());
        }

        #[test]
        fn test_transpose(x in any::<Result<Option<u8>, u8>>()) {
            prop_assert!(x.inject().transpose() == x.transpose().inject());
        }

        #[test]
        fn test_flatten(x in any::<Result<Result<u8, u8>, u8>>(), is_ok in any::<bool>()) {
            prop_assert!(x.inject().flatten() == x.flatten().inject());
        }

        // The model's `PartialEq for Result` is aeneas/lean-only.
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_eq(x in any::<Result<u8, u8>>(), y in any::<Result<u8, u8>>()) {
            prop_assert_eq!(
                crate::cmp::PartialEq::eq(&x.clone().inject(), &y.clone().inject()),
                x == y
            );
        }

        // `x == x` exercises the equal-payload `(Ok, Ok)` / `(Err, Err)` arms;
        // two independent draws hit an equal `Err` pair about once in 512.
        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_eq_reflexive(x in any::<Result<u8, u8>>()) {
            prop_assert!(crate::cmp::PartialEq::eq(
                &x.clone().inject(),
                &x.clone().inject()
            ));
        }

        // ----- Try (from_output / branch) -----------------------------------
        // std's `Try` is unstable, so these pin the model's documented
        // semantics (which mirror `?`): `from_output` injects into `Ok`,
        // `branch` sends `Ok(v)` to `Continue(v)` and `Err(e)` to `Break(Err(e))`.

        // Only the in-domain half: std's versions are UB on the other variant.

        #[test]
        fn test_unwrap_unchecked(v in any::<u8>()) {
            let res: Result<u8, u8> = Ok(v);
            prop_assert_eq!(
                unsafe { res.clone().inject().unwrap_unchecked() },
                unsafe { res.unwrap_unchecked() }
            );
        }

        #[test]
        fn test_unwrap_err_unchecked(e in any::<u8>()) {
            let res: Result<u8, u8> = Err(e);
            prop_assert_eq!(
                unsafe { res.clone().inject().unwrap_err_unchecked() },
                unsafe { res.unwrap_err_unchecked() }
            );
        }

        #[test]
        fn test_unwrap_unchecked_on_err_panics(e in any::<u8>()) {
            let res: super::Result<u8, u8> = super::Result::Err(e);
            let panicked = std::panic::catch_unwind(|| unsafe { res.unwrap_unchecked() }).is_err();
            prop_assert!(panicked);
        }

        #[test]
        fn test_unwrap_err_unchecked_on_ok_panics(v in any::<u8>()) {
            let res: super::Result<u8, u8> = super::Result::Ok(v);
            let panicked =
                std::panic::catch_unwind(|| unsafe { res.unwrap_err_unchecked() }).is_err();
            prop_assert!(panicked);
        }

        #[test]
        fn test_iter(x in any::<Result<u8, u8>>()) {
            let model = x.clone().inject();
            prop_assert_eq!(
                drain(model.iter()).into_iter().copied().collect::<Vec<u8>>(),
                x.iter().copied().collect::<Vec<u8>>()
            );
        }

        #[test]
        fn test_into_iter(x in any::<Result<u8, u8>>()) {
            use crate::iter::traits::collect::IntoIterator as ModelIntoIterator;
            let model = <super::Result<u8, u8> as ModelIntoIterator>::into_iter(x.clone().inject());
            prop_assert_eq!(drain(model), x.into_iter().collect::<Vec<u8>>());
        }

        #[test]
        fn test_as_deref(x in any::<Result<u8, u8>>()) {
            let std_res: Result<&u8, u8> = match &x {
                Ok(v) => Ok(v),
                Err(e) => Err(*e),
            };
            let model: super::Result<&u8, u8> = match &x {
                Ok(v) => super::Result::Ok(v),
                Err(e) => super::Result::Err(*e),
            };
            prop_assert_eq!(
                model.as_deref().map(|v: &u8| *v).map_err(|e: &u8| *e),
                std_res.as_deref().map(|v| *v).map_err(|e| *e).inject()
            );
        }

        #[cfg(not(hax_backend_fstar))]
        #[test]
        fn test_as_deref_mut(v in any::<u8>(), e in any::<u8>(), is_ok in any::<bool>()) {
            let mut std_res: Result<u8, u8> = if is_ok { Ok(v) } else { Err(e) };
            let mut model: super::Result<Cell, u8> = if is_ok {
                super::Result::Ok(Cell(v))
            } else {
                super::Result::Err(e)
            };
            if let Ok(r) = std_res.as_mut() {
                *r = r.wrapping_add(1);
            }
            prop_assert_eq!(*crate::ops::deref::Deref::deref(&Cell(v)), v);
            if let super::Result::Ok(r) = model.as_deref_mut() {
                *r = r.wrapping_add(1);
            }
            prop_assert_eq!(model.map(|c: Cell| c.0), std_res.inject());
        }

        #[test]
        fn test_copied(x in any::<Result<u8, u8>>()) {
            let model: super::Result<&u8, u8> = match &x {
                Ok(v) => super::Result::Ok(v),
                Err(e) => super::Result::Err(*e),
            };
            prop_assert_eq!(
                model.copied(),
                x.as_ref().map(|v| *v).map_err(|e| *e).inject()
            );
        }

        #[test]
        fn test_try_from_output(v in any::<u8>()) {
            use crate::ops::try_trait::Try;
            prop_assert_eq!(
                <super::Result<u8, u8> as Try>::from_output(v),
                super::Result::Ok(v)
            );
        }

        #[test]
        fn test_try_branch_ok(v in any::<u8>()) {
            use crate::ops::try_trait::Try;
            use crate::ops::control_flow::ControlFlow;
            let r: super::Result<u8, u8> = super::Result::Ok(v);
            match r.branch() {
                ControlFlow::Continue(c) => prop_assert_eq!(c, v),
                ControlFlow::Break(_) => prop_assert!(false, "Ok should Continue"),
            }
        }

        #[test]
        fn test_try_branch_err(e in any::<u8>()) {
            use crate::ops::try_trait::Try;
            use crate::ops::control_flow::ControlFlow;
            let r: super::Result<u8, u8> = super::Result::Err(e);
            match r.branch() {
                // `Break` carries the residual `Result<Infallible, u8>`; match
                // the `Err` arm to read the error without needing `Infallible: Eq`.
                ControlFlow::Break(super::Result::Err(ee)) => prop_assert_eq!(ee, e),
                _ => prop_assert!(false, "Err should Break(Err(e))"),
            }
        }

        #[test]
        fn test_as_mut(x in any::<Result<u8, u8>>()) {
            let mut model = x.clone().inject();
            let mut std_value = x.clone();
            match (model.as_mut(), std_value.as_mut()) {
                (super::Ok(m), Ok(s)) => { *m = 1; *s = 1; }
                (super::Err(m), Err(s)) => { *m = 2; *s = 2; }
                _ => prop_assert!(false, "as_mut changed the variant"),
            }
            prop_assert_eq!(model, std_value.inject());
        }

        #[test]
        fn test_inspect(x in any::<Result<u8, u8>>()) {
            let model_seen = std::cell::Cell::new(0u8);
            let model = x.clone().inject().inspect(|v: &u8| model_seen.set(*v));
            let std_seen = std::cell::Cell::new(0u8);
            let std_value = x.clone().inspect(|v: &u8| std_seen.set(*v));
            prop_assert_eq!(model_seen.get(), std_seen.get());
            prop_assert_eq!(model, std_value.inject());
        }

        #[test]
        fn test_inspect_err(x in any::<Result<u8, u8>>()) {
            let model_seen = std::cell::Cell::new(0u8);
            let model = x.clone().inject().inspect_err(|e: &u8| model_seen.set(*e));
            let std_seen = std::cell::Cell::new(0u8);
            let std_value = x.clone().inspect_err(|e: &u8| std_seen.set(*e));
            prop_assert_eq!(model_seen.get(), std_seen.get());
            prop_assert_eq!(model, std_value.inject());
        }

        // `?` on an `Err`: re-inject the residual, widening `u8` to `u16`.
        #[test]
        fn test_from_residual(e in any::<u8>()) {
            use crate::ops::try_trait::FromResidual;
            let residual: super::Result<crate::convert::Infallible, u8> = super::Err(e);
            let widened: super::Result<u8, u16> = FromResidual::from_residual(residual);
            prop_assert_eq!(widened, super::Err(e as u16));
        }
    }

    // The `Ok(_)` arm of `from_residual` is unreachable for a real residual (its
    // payload would have to be an `Infallible`), so it can only be run directly.
    #[test]
    #[should_panic]
    fn test_from_residual_ok_panics() {
        use crate::ops::try_trait::FromResidual;
        let residual: super::Result<crate::convert::Infallible, u8> =
            super::Ok(crate::convert::Infallible);
        let _: super::Result<u8, u16> = FromResidual::from_residual(residual);
    }

    #[test]
    fn test_unwrap_on_err_panics() {
        crate::testing::panics_like_core(
            || super::Result::<u8, u8>::Err(1).unwrap(),
            || Err::<u8, u8>(1).unwrap(),
        );
    }

    #[test]
    fn test_expect_on_err_panics() {
        crate::testing::panics_like_core(
            || super::Result::<u8, u8>::Err(1).expect("boom"),
            || Err::<u8, u8>(1).expect("boom"),
        );
    }

    #[test]
    fn test_unwrap_err_on_ok_panics() {
        crate::testing::panics_like_core(
            || super::Result::<u8, u8>::Ok(1).unwrap_err(),
            || Ok::<u8, u8>(1).unwrap_err(),
        );
    }

    #[test]
    fn test_expect_err_on_ok_panics() {
        crate::testing::panics_like_core(
            || super::Result::<u8, u8>::Ok(1).expect_err("boom"),
            || Ok::<u8, u8>(1).expect_err("boom"),
        );
    }
}

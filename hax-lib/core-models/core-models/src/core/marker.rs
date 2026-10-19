use super::clone::Clone;

/// See [`std::marker::Copy`]
pub trait Copy: Clone {}
/// See [`std::marker::Send`]
pub trait Send {}
/// See [`std::marker::Sync`]
pub trait Sync {}
/// See [`std::marker::Sized`]
pub trait Sized: MetaSized {}
/// See [`std::marker::StructuralPartialEq`]
pub trait StructuralPartialEq {}

// In our models, all types implement those marker traits
impl<T> Send for T {}
impl<T> Sync for T {}
impl<T> Sized for T {}
// The F* model; the other backends use the per-integer impls below.
#[cfg(hax_backend_fstar)]
impl<T: Clone> Copy for T {}

macro_rules! copy_impl_for_int {
    ($($t:ty),*) => {
        $(
            impl Copy for $t {}
        )*
    };
}

#[cfg(not(hax_backend_fstar))]
copy_impl_for_int!(
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

// Every type is `MetaSized` and `PointeeSized`, as every type is `Sized`. Placed
// after the impls above so that those keep their extracted names.
impl<T> MetaSized for T {}
impl<T> PointeeSized for T {}

/// See [`std::marker::PhantomData`]
#[hax_lib::fstar::replace("type t_PhantomData (v_T: Type0) = | PhantomData : t_PhantomData v_T")]
#[hax_lib::legacy_lean::replace("structure PhantomData (T : Type) where")]
struct PhantomData<T>(T);

/// See [`std::marker::MetaSized`]
pub trait MetaSized: PointeeSized {}
/// See [`std::marker::PointeeSized`]
pub trait PointeeSized {}

// Empty markers without impls, declared so that signatures mentioning them resolve.

/// See [`std::marker::Unsize`]
pub trait Unsize<T> {}
/// See [`std::marker::Freeze`]
pub trait Freeze {}
/// See [`std::marker::Unpin`]
pub trait Unpin {}
/// See [`std::marker::Destruct`]
pub trait Destruct {}
/// See [`std::marker::Tuple`]
pub trait Tuple {}
/// See [`std::marker::ConstParamTy_`]
//
// DEVIATION(std): no `Eq` supertrait; it would close an F* module cycle via `Cmp`.
pub trait ConstParamTy_: StructuralPartialEq {}

/// See [`std::marker::FnPtr`]
pub trait FnPtr: Copy {}

/// See [`std::marker::DiscriminantKind`]
#[cfg(not(hax_backend_fstar))]
pub trait DiscriminantKind {
    /// See [`std::marker::DiscriminantKind::Discriminant`]
    type Discriminant: Clone
        + Copy
        + crate::fmt::Debug
        + crate::cmp::Eq
        + crate::cmp::PartialEq<Self::Discriminant>
        + crate::hash::Hash
        + Send
        + Sync
        + Unpin;
}
/// See [`std::marker::DiscriminantKind`]
//
// DEVIATION(std): no bounds on `Discriminant` in F*. `Hash` and `Debug` would make
// this module and `hash`/`fmt` depend on each other, a module cycle F* rejects.
#[cfg(hax_backend_fstar)]
pub trait DiscriminantKind {
    /// See [`std::marker::DiscriminantKind::Discriminant`]
    type Discriminant;
}

/// See [`std::marker::PhantomPinned`]
pub struct PhantomPinned;

// The impls real core derives on `PhantomPinned`. Its negative `Unpin` impl has no
// counterpart, as the model has no negative impls. Under F*, `Debug`, `Clone` and
// `Copy` come from the blanket impls.
#[cfg(not(hax_backend_fstar))]
impl crate::fmt::Debug for PhantomPinned {
    fn fmt(&self, f: &mut crate::fmt::Formatter) -> crate::fmt::Result {
        crate::fmt::Result::Ok(())
    }
}
impl crate::default::Default for PhantomPinned {
    fn default() -> PhantomPinned {
        PhantomPinned
    }
}
#[cfg(not(hax_backend_fstar))]
impl Copy for PhantomPinned {}
#[cfg(not(hax_backend_fstar))]
impl Clone for PhantomPinned {
    fn clone(&self) -> PhantomPinned {
        PhantomPinned
    }
    // Overridden, not left to the default: charon only emits the per-impl
    // `clone_from` symbol when the impl overrides it, and clients resolve to it.
    fn clone_from(self, source: PhantomPinned) -> PhantomPinned {
        source
    }
}
impl StructuralPartialEq for PhantomPinned {}
// DEVIATION(std): no comparison or `Hash` impls in F*. They would make this
// module depend on `cmp`, `option` and `hash`, which depend on it: a module
// cycle F* rejects.
#[cfg(not(hax_backend_fstar))]
impl crate::cmp::Eq for PhantomPinned {}
#[cfg(not(hax_backend_fstar))]
impl crate::cmp::PartialEq<PhantomPinned> for PhantomPinned {
    fn eq(&self, other: &PhantomPinned) -> bool {
        true
    }
    fn ne(&self, other: &PhantomPinned) -> bool {
        false
    }
}
#[cfg(not(hax_backend_fstar))]
impl crate::cmp::Ord for PhantomPinned {
    fn cmp(&self, other: &PhantomPinned) -> crate::cmp::Ordering {
        crate::cmp::Ordering::Equal
    }
}
#[cfg(not(hax_backend_fstar))]
impl crate::cmp::PartialOrd<PhantomPinned> for PhantomPinned {
    fn partial_cmp(&self, other: &PhantomPinned) -> crate::option::Option<crate::cmp::Ordering> {
        crate::option::Option::Some(crate::cmp::Ordering::Equal)
    }
}
#[cfg(not(hax_backend_fstar))]
impl crate::hash::Hash for PhantomPinned {
    fn hash<H: crate::hash::Hasher>(&self, state: &mut H) {}
}

pub use self::variance::{
    PhantomContravariant, PhantomContravariantLifetime, PhantomCovariant, PhantomCovariantLifetime,
    PhantomInvariant, PhantomInvariantLifetime, Variance, variance,
};

/// The variance markers, in a submodule as in core, for their extracted names.
//
// DEVIATION(std): all wrap `PhantomData<T>`; variance has no meaning in the model.
mod variance {
    /// See [`std::marker::Variance`]
    //
    // DEVIATION(std): no `Sealed` supertrait with its `const VALUE: Self`, so
    // `variance()` returns `Default::default()` instead; the value is the same.
    pub trait Variance: crate::default::Default {}

    /// See [`std::marker::variance`]
    pub fn variance<T: Variance>() -> T {
        <T as crate::default::Default>::default()
    }

    /// See [`std::marker::PhantomCovariant`]
    pub struct PhantomCovariant<T>(std::marker::PhantomData<T>);
    /// See [`std::marker::PhantomContravariant`]
    pub struct PhantomContravariant<T>(std::marker::PhantomData<T>);
    /// See [`std::marker::PhantomInvariant`]
    pub struct PhantomInvariant<T>(std::marker::PhantomData<T>);
    /// See [`std::marker::PhantomCovariantLifetime`]
    pub struct PhantomCovariantLifetime<'a>(PhantomCovariant<&'a ()>);
    /// See [`std::marker::PhantomContravariantLifetime`]
    pub struct PhantomContravariantLifetime<'a>(PhantomContravariant<&'a ()>);
    /// See [`std::marker::PhantomInvariantLifetime`]
    pub struct PhantomInvariantLifetime<'a>(PhantomInvariant<&'a ()>);

    // hax names impls after their position among the module's impls, so the impls
    // below follow real core's order, with an empty impl wherever the model has
    // no counterpart: core's private `Sealed` impls, and under F* the `Debug`,
    // `Clone` and `Copy` impls, which F*'s blanket impls already provide. rustc
    // numbers impls without an attribute macro first, hence `hax_lib::attributes`
    // on every impl.
    #[hax_lib::attributes]
    impl<'a> PhantomCovariantLifetime<'a> {
        /// See [`std::marker::PhantomCovariantLifetime::new`]
        pub fn new() -> PhantomCovariantLifetime<'a> {
            PhantomCovariantLifetime(PhantomCovariant::new())
        }
    }
    #[hax_lib::attributes]
    impl<'a> PhantomCovariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> Variance for PhantomCovariantLifetime<'a> {}
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::attributes]
    impl<'a> crate::fmt::Debug for PhantomCovariantLifetime<'a> {
        fn fmt(&self, f: &mut crate::fmt::Formatter) -> crate::fmt::Result {
            crate::fmt::Result::Ok(())
        }
    }
    #[cfg(hax_backend_fstar)]
    #[hax_lib::attributes]
    impl<'a> PhantomCovariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomContravariantLifetime<'a> {
        /// See [`std::marker::PhantomContravariantLifetime::new`]
        pub fn new() -> PhantomContravariantLifetime<'a> {
            PhantomContravariantLifetime(PhantomContravariant::new())
        }
    }
    #[hax_lib::attributes]
    impl<'a> PhantomContravariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> Variance for PhantomContravariantLifetime<'a> {}
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::attributes]
    impl<'a> crate::fmt::Debug for PhantomContravariantLifetime<'a> {
        fn fmt(&self, f: &mut crate::fmt::Formatter) -> crate::fmt::Result {
            crate::fmt::Result::Ok(())
        }
    }
    #[cfg(hax_backend_fstar)]
    #[hax_lib::attributes]
    impl<'a> PhantomContravariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {
        /// See [`std::marker::PhantomInvariantLifetime::new`]
        pub fn new() -> PhantomInvariantLifetime<'a> {
            PhantomInvariantLifetime(PhantomInvariant::new())
        }
    }
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> Variance for PhantomInvariantLifetime<'a> {}
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::attributes]
    impl<'a> crate::fmt::Debug for PhantomInvariantLifetime<'a> {
        fn fmt(&self, f: &mut crate::fmt::Formatter) -> crate::fmt::Result {
            crate::fmt::Result::Ok(())
        }
    }
    #[cfg(hax_backend_fstar)]
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    // Real core derives these on the lifetime markers. The derived impls go through
    // the zero-sized field; the bodies below compute the same results directly, as
    // the Lean extraction erases the field's type.
    #[hax_lib::attributes]
    impl<'a> crate::default::Default for PhantomCovariantLifetime<'a> {
        fn default() -> PhantomCovariantLifetime<'a> {
            PhantomCovariantLifetime::new()
        }
    }
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::attributes]
    impl<'a> crate::clone::Clone for PhantomCovariantLifetime<'a> {
        fn clone(&self) -> PhantomCovariantLifetime<'a> {
            PhantomCovariantLifetime::new()
        }
        // Overridden, not left to the default: charon only emits the per-impl
        // `clone_from` symbol when the impl overrides it, and clients resolve to it.
        fn clone_from(self, source: PhantomCovariantLifetime<'a>) -> PhantomCovariantLifetime<'a> {
            source
        }
    }
    #[cfg(hax_backend_fstar)]
    #[hax_lib::attributes]
    impl<'a> PhantomCovariantLifetime<'a> {}
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::attributes]
    impl<'a> super::Copy for PhantomCovariantLifetime<'a> {}
    #[cfg(hax_backend_fstar)]
    #[hax_lib::attributes]
    impl<'a> PhantomCovariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> super::StructuralPartialEq for PhantomCovariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> crate::cmp::PartialEq<PhantomCovariantLifetime<'a>> for PhantomCovariantLifetime<'a> {
        fn eq(&self, other: &PhantomCovariantLifetime<'a>) -> bool {
            true
        }
        #[cfg(not(hax_backend_fstar))]
        fn ne(&self, other: &PhantomCovariantLifetime<'a>) -> bool {
            false
        }
    }
    #[hax_lib::attributes]
    impl<'a> crate::cmp::Eq for PhantomCovariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> crate::cmp::PartialOrd<PhantomCovariantLifetime<'a>> for PhantomCovariantLifetime<'a> {
        fn partial_cmp(
            &self,
            other: &PhantomCovariantLifetime<'a>,
        ) -> crate::option::Option<crate::cmp::Ordering> {
            crate::option::Option::Some(crate::cmp::Ordering::Equal)
        }
    }
    #[hax_lib::attributes]
    impl<'a> crate::cmp::Ord for PhantomCovariantLifetime<'a> {
        fn cmp(&self, other: &PhantomCovariantLifetime<'a>) -> crate::cmp::Ordering {
            crate::cmp::Ordering::Equal
        }
    }
    #[hax_lib::attributes]
    impl<'a> crate::hash::Hash for PhantomCovariantLifetime<'a> {
        fn hash<H: crate::hash::Hasher>(&self, state: &mut H) {}
    }
    #[hax_lib::attributes]
    impl<'a> crate::default::Default for PhantomContravariantLifetime<'a> {
        fn default() -> PhantomContravariantLifetime<'a> {
            PhantomContravariantLifetime::new()
        }
    }
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::attributes]
    impl<'a> crate::clone::Clone for PhantomContravariantLifetime<'a> {
        fn clone(&self) -> PhantomContravariantLifetime<'a> {
            PhantomContravariantLifetime::new()
        }
        // Overridden, not left to the default: charon only emits the per-impl
        // `clone_from` symbol when the impl overrides it, and clients resolve to it.
        fn clone_from(
            self,
            source: PhantomContravariantLifetime<'a>,
        ) -> PhantomContravariantLifetime<'a> {
            source
        }
    }
    #[cfg(hax_backend_fstar)]
    #[hax_lib::attributes]
    impl<'a> PhantomContravariantLifetime<'a> {}
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::attributes]
    impl<'a> super::Copy for PhantomContravariantLifetime<'a> {}
    #[cfg(hax_backend_fstar)]
    #[hax_lib::attributes]
    impl<'a> PhantomContravariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> super::StructuralPartialEq for PhantomContravariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> crate::cmp::PartialEq<PhantomContravariantLifetime<'a>>
        for PhantomContravariantLifetime<'a>
    {
        fn eq(&self, other: &PhantomContravariantLifetime<'a>) -> bool {
            true
        }
        #[cfg(not(hax_backend_fstar))]
        fn ne(&self, other: &PhantomContravariantLifetime<'a>) -> bool {
            false
        }
    }
    #[hax_lib::attributes]
    impl<'a> crate::cmp::Eq for PhantomContravariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> crate::cmp::PartialOrd<PhantomContravariantLifetime<'a>>
        for PhantomContravariantLifetime<'a>
    {
        fn partial_cmp(
            &self,
            other: &PhantomContravariantLifetime<'a>,
        ) -> crate::option::Option<crate::cmp::Ordering> {
            crate::option::Option::Some(crate::cmp::Ordering::Equal)
        }
    }
    #[hax_lib::attributes]
    impl<'a> crate::cmp::Ord for PhantomContravariantLifetime<'a> {
        fn cmp(&self, other: &PhantomContravariantLifetime<'a>) -> crate::cmp::Ordering {
            crate::cmp::Ordering::Equal
        }
    }
    #[hax_lib::attributes]
    impl<'a> crate::hash::Hash for PhantomContravariantLifetime<'a> {
        fn hash<H: crate::hash::Hasher>(&self, state: &mut H) {}
    }
    #[hax_lib::attributes]
    impl<'a> crate::default::Default for PhantomInvariantLifetime<'a> {
        fn default() -> PhantomInvariantLifetime<'a> {
            PhantomInvariantLifetime::new()
        }
    }
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::attributes]
    impl<'a> crate::clone::Clone for PhantomInvariantLifetime<'a> {
        fn clone(&self) -> PhantomInvariantLifetime<'a> {
            PhantomInvariantLifetime::new()
        }
        // Overridden, not left to the default: charon only emits the per-impl
        // `clone_from` symbol when the impl overrides it, and clients resolve to it.
        fn clone_from(self, source: PhantomInvariantLifetime<'a>) -> PhantomInvariantLifetime<'a> {
            source
        }
    }
    #[cfg(hax_backend_fstar)]
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::attributes]
    impl<'a> super::Copy for PhantomInvariantLifetime<'a> {}
    #[cfg(hax_backend_fstar)]
    #[hax_lib::attributes]
    impl<'a> PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> super::StructuralPartialEq for PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> crate::cmp::PartialEq<PhantomInvariantLifetime<'a>> for PhantomInvariantLifetime<'a> {
        fn eq(&self, other: &PhantomInvariantLifetime<'a>) -> bool {
            true
        }
        #[cfg(not(hax_backend_fstar))]
        fn ne(&self, other: &PhantomInvariantLifetime<'a>) -> bool {
            false
        }
    }
    #[hax_lib::attributes]
    impl<'a> crate::cmp::Eq for PhantomInvariantLifetime<'a> {}
    #[hax_lib::attributes]
    impl<'a> crate::cmp::PartialOrd<PhantomInvariantLifetime<'a>> for PhantomInvariantLifetime<'a> {
        fn partial_cmp(
            &self,
            other: &PhantomInvariantLifetime<'a>,
        ) -> crate::option::Option<crate::cmp::Ordering> {
            crate::option::Option::Some(crate::cmp::Ordering::Equal)
        }
    }
    #[hax_lib::attributes]
    impl<'a> crate::cmp::Ord for PhantomInvariantLifetime<'a> {
        fn cmp(&self, other: &PhantomInvariantLifetime<'a>) -> crate::cmp::Ordering {
            crate::cmp::Ordering::Equal
        }
    }
    #[hax_lib::attributes]
    impl<'a> crate::hash::Hash for PhantomInvariantLifetime<'a> {
        fn hash<H: crate::hash::Hasher>(&self, state: &mut H) {}
    }
    #[hax_lib::attributes]
    impl<T> PhantomCovariant<T> {
        /// See [`std::marker::PhantomCovariant::new`]
        pub fn new() -> PhantomCovariant<T> {
            PhantomCovariant(std::marker::PhantomData)
        }
    }
    #[hax_lib::attributes]
    impl<T> PhantomCovariant<T> {}
    #[hax_lib::attributes]
    impl<T> Variance for PhantomCovariant<T> {}
    #[hax_lib::attributes]
    impl<T> crate::default::Default for PhantomCovariant<T> {
        fn default() -> PhantomCovariant<T> {
            PhantomCovariant(std::marker::PhantomData)
        }
    }
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::attributes]
    impl<T> crate::fmt::Debug for PhantomCovariant<T> {
        fn fmt(&self, f: &mut crate::fmt::Formatter) -> crate::fmt::Result {
            crate::fmt::Result::Ok(())
        }
    }
    #[cfg(hax_backend_fstar)]
    #[hax_lib::attributes]
    impl<T> PhantomCovariant<T> {}
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::attributes]
    impl<T> crate::clone::Clone for PhantomCovariant<T> {
        fn clone(&self) -> PhantomCovariant<T> {
            PhantomCovariant(std::marker::PhantomData)
        }
        // Overridden, not left to the default: charon only emits the per-impl
        // `clone_from` symbol when the impl overrides it, and clients resolve to it.
        fn clone_from(self, source: PhantomCovariant<T>) -> PhantomCovariant<T> {
            source
        }
    }
    #[cfg(hax_backend_fstar)]
    #[hax_lib::attributes]
    impl<T> PhantomCovariant<T> {}
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::attributes]
    impl<T> super::Copy for PhantomCovariant<T> {}
    #[cfg(hax_backend_fstar)]
    #[hax_lib::attributes]
    impl<T> PhantomCovariant<T> {}
    #[hax_lib::attributes]
    impl<T> crate::cmp::PartialEq<PhantomCovariant<T>> for PhantomCovariant<T> {
        fn eq(&self, other: &PhantomCovariant<T>) -> bool {
            true
        }
        #[cfg(not(hax_backend_fstar))]
        fn ne(&self, other: &PhantomCovariant<T>) -> bool {
            false
        }
    }
    #[hax_lib::attributes]
    impl<T> crate::cmp::Eq for PhantomCovariant<T> {}
    #[hax_lib::attributes]
    impl<T> crate::cmp::PartialOrd<PhantomCovariant<T>> for PhantomCovariant<T> {
        fn partial_cmp(
            &self,
            other: &PhantomCovariant<T>,
        ) -> crate::option::Option<crate::cmp::Ordering> {
            crate::option::Option::Some(crate::cmp::Ordering::Equal)
        }
    }
    #[hax_lib::attributes]
    impl<T> crate::cmp::Ord for PhantomCovariant<T> {
        fn cmp(&self, other: &PhantomCovariant<T>) -> crate::cmp::Ordering {
            crate::cmp::Ordering::Equal
        }
    }
    #[hax_lib::attributes]
    impl<T> crate::hash::Hash for PhantomCovariant<T> {
        fn hash<H: crate::hash::Hasher>(&self, state: &mut H) {}
    }
    #[hax_lib::attributes]
    impl<T> PhantomContravariant<T> {
        /// See [`std::marker::PhantomContravariant::new`]
        pub fn new() -> PhantomContravariant<T> {
            PhantomContravariant(std::marker::PhantomData)
        }
    }
    #[hax_lib::attributes]
    impl<T> PhantomContravariant<T> {}
    #[hax_lib::attributes]
    impl<T> Variance for PhantomContravariant<T> {}
    #[hax_lib::attributes]
    impl<T> crate::default::Default for PhantomContravariant<T> {
        fn default() -> PhantomContravariant<T> {
            PhantomContravariant(std::marker::PhantomData)
        }
    }
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::attributes]
    impl<T> crate::fmt::Debug for PhantomContravariant<T> {
        fn fmt(&self, f: &mut crate::fmt::Formatter) -> crate::fmt::Result {
            crate::fmt::Result::Ok(())
        }
    }
    #[cfg(hax_backend_fstar)]
    #[hax_lib::attributes]
    impl<T> PhantomContravariant<T> {}
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::attributes]
    impl<T> crate::clone::Clone for PhantomContravariant<T> {
        fn clone(&self) -> PhantomContravariant<T> {
            PhantomContravariant(std::marker::PhantomData)
        }
        // Overridden, not left to the default: charon only emits the per-impl
        // `clone_from` symbol when the impl overrides it, and clients resolve to it.
        fn clone_from(self, source: PhantomContravariant<T>) -> PhantomContravariant<T> {
            source
        }
    }
    #[cfg(hax_backend_fstar)]
    #[hax_lib::attributes]
    impl<T> PhantomContravariant<T> {}
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::attributes]
    impl<T> super::Copy for PhantomContravariant<T> {}
    #[cfg(hax_backend_fstar)]
    #[hax_lib::attributes]
    impl<T> PhantomContravariant<T> {}
    #[hax_lib::attributes]
    impl<T> crate::cmp::PartialEq<PhantomContravariant<T>> for PhantomContravariant<T> {
        fn eq(&self, other: &PhantomContravariant<T>) -> bool {
            true
        }
        #[cfg(not(hax_backend_fstar))]
        fn ne(&self, other: &PhantomContravariant<T>) -> bool {
            false
        }
    }
    #[hax_lib::attributes]
    impl<T> crate::cmp::Eq for PhantomContravariant<T> {}
    #[hax_lib::attributes]
    impl<T> crate::cmp::PartialOrd<PhantomContravariant<T>> for PhantomContravariant<T> {
        fn partial_cmp(
            &self,
            other: &PhantomContravariant<T>,
        ) -> crate::option::Option<crate::cmp::Ordering> {
            crate::option::Option::Some(crate::cmp::Ordering::Equal)
        }
    }
    #[hax_lib::attributes]
    impl<T> crate::cmp::Ord for PhantomContravariant<T> {
        fn cmp(&self, other: &PhantomContravariant<T>) -> crate::cmp::Ordering {
            crate::cmp::Ordering::Equal
        }
    }
    #[hax_lib::attributes]
    impl<T> crate::hash::Hash for PhantomContravariant<T> {
        fn hash<H: crate::hash::Hasher>(&self, state: &mut H) {}
    }
    #[hax_lib::attributes]
    impl<T> PhantomInvariant<T> {
        /// See [`std::marker::PhantomInvariant::new`]
        pub fn new() -> PhantomInvariant<T> {
            PhantomInvariant(std::marker::PhantomData)
        }
    }
    #[hax_lib::attributes]
    impl<T> PhantomInvariant<T> {}
    #[hax_lib::attributes]
    impl<T> Variance for PhantomInvariant<T> {}
    #[hax_lib::attributes]
    impl<T> crate::default::Default for PhantomInvariant<T> {
        fn default() -> PhantomInvariant<T> {
            PhantomInvariant(std::marker::PhantomData)
        }
    }
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::attributes]
    impl<T> crate::fmt::Debug for PhantomInvariant<T> {
        fn fmt(&self, f: &mut crate::fmt::Formatter) -> crate::fmt::Result {
            crate::fmt::Result::Ok(())
        }
    }
    #[cfg(hax_backend_fstar)]
    #[hax_lib::attributes]
    impl<T> PhantomInvariant<T> {}
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::attributes]
    impl<T> crate::clone::Clone for PhantomInvariant<T> {
        fn clone(&self) -> PhantomInvariant<T> {
            PhantomInvariant(std::marker::PhantomData)
        }
        // Overridden, not left to the default: charon only emits the per-impl
        // `clone_from` symbol when the impl overrides it, and clients resolve to it.
        fn clone_from(self, source: PhantomInvariant<T>) -> PhantomInvariant<T> {
            source
        }
    }
    #[cfg(hax_backend_fstar)]
    #[hax_lib::attributes]
    impl<T> PhantomInvariant<T> {}
    #[cfg(not(hax_backend_fstar))]
    #[hax_lib::attributes]
    impl<T> super::Copy for PhantomInvariant<T> {}
    #[cfg(hax_backend_fstar)]
    #[hax_lib::attributes]
    impl<T> PhantomInvariant<T> {}
    #[hax_lib::attributes]
    impl<T> crate::cmp::PartialEq<PhantomInvariant<T>> for PhantomInvariant<T> {
        fn eq(&self, other: &PhantomInvariant<T>) -> bool {
            true
        }
        #[cfg(not(hax_backend_fstar))]
        fn ne(&self, other: &PhantomInvariant<T>) -> bool {
            false
        }
    }
    #[hax_lib::attributes]
    impl<T> crate::cmp::Eq for PhantomInvariant<T> {}
    #[hax_lib::attributes]
    impl<T> crate::cmp::PartialOrd<PhantomInvariant<T>> for PhantomInvariant<T> {
        fn partial_cmp(
            &self,
            other: &PhantomInvariant<T>,
        ) -> crate::option::Option<crate::cmp::Ordering> {
            crate::option::Option::Some(crate::cmp::Ordering::Equal)
        }
    }
    #[hax_lib::attributes]
    impl<T> crate::cmp::Ord for PhantomInvariant<T> {
        fn cmp(&self, other: &PhantomInvariant<T>) -> crate::cmp::Ordering {
            crate::cmp::Ordering::Equal
        }
    }
    #[hax_lib::attributes]
    impl<T> crate::hash::Hash for PhantomInvariant<T> {
        fn hash<H: crate::hash::Hasher>(&self, state: &mut H) {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testing::Inject;

    /// Byte-log hasher implementing both the model's and std's `Hasher`.
    #[derive(Debug, PartialEq)]
    struct Log(Vec<u8>);

    impl crate::hash::Hasher for Log {
        fn finish(&self) -> u64 {
            0
        }
        fn write(&mut self, bytes: &[u8]) {
            self.0.extend_from_slice(bytes)
        }
    }

    impl std::hash::Hasher for Log {
        fn finish(&self) -> u64 {
            0
        }
        fn write(&mut self, bytes: &[u8]) {
            self.0.extend_from_slice(bytes)
        }
    }

    // Each model marker against std's: layout, the constructors, and the trait
    // impls std provides. Two markers of a type are always equal, so the impls
    // are compared on a pair built by `new` and `default`.
    macro_rules! variance_marker_tests {
        ($($test:ident: $model:ty, $std:ty;)*) => {$(
            #[test]
            fn $test() {
                assert_eq!(std::mem::size_of::<$model>(), std::mem::size_of::<$std>());

                let (m, n): ($model, $model) = (<$model>::new(), crate::default::Default::default());
                let (s, t): ($std, $std) = (<$std>::new(), std::default::Default::default());
                let v: $model = variance();
                assert!(crate::cmp::PartialEq::eq(&v, &m));

                assert_eq!(crate::cmp::PartialEq::eq(&m, &n), s == t);
                assert_eq!(
                    crate::cmp::PartialOrd::partial_cmp(&m, &n),
                    std::cmp::PartialOrd::partial_cmp(&s, &t).inject()
                );
                assert_eq!(crate::cmp::Ord::cmp(&m, &n), std::cmp::Ord::cmp(&s, &t).inject());

                let mut mh = Log(Vec::new());
                crate::hash::Hash::hash(&m, &mut mh);
                let mut sh = Log(Vec::new());
                std::hash::Hash::hash(&s, &mut sh);
                assert_eq!(mh, sh);
            }
        )*};
    }

    variance_marker_tests! {
        test_phantom_covariant: PhantomCovariant<u8>, std::marker::PhantomCovariant<u8>;
        test_phantom_contravariant: PhantomContravariant<u8>, std::marker::PhantomContravariant<u8>;
        test_phantom_invariant: PhantomInvariant<u8>, std::marker::PhantomInvariant<u8>;
        test_phantom_covariant_lifetime:
            PhantomCovariantLifetime<'static>, std::marker::PhantomCovariantLifetime<'static>;
        test_phantom_contravariant_lifetime:
            PhantomContravariantLifetime<'static>, std::marker::PhantomContravariantLifetime<'static>;
        test_phantom_invariant_lifetime:
            PhantomInvariantLifetime<'static>, std::marker::PhantomInvariantLifetime<'static>;
    }

    // The impls F* takes from its blanket `Clone` and `Debug` instead. The model's
    // `Formatter` renders nothing, so only success is observable for `Debug`.
    macro_rules! variance_marker_tests_not_fstar {
        ($($test:ident: $model:ty, $std:ty;)*) => {$(
            #[cfg(not(hax_backend_fstar))]
            #[test]
            fn $test() {
                let m = <$model>::new();
                let s = <$std>::new();
                assert_eq!(
                    crate::cmp::PartialEq::ne(&m, &crate::clone::Clone::clone(&m)),
                    s != std::clone::Clone::clone(&s)
                );
                let m = crate::clone::Clone::clone_from(m, <$model>::new());
                assert!(crate::cmp::PartialEq::eq(&m, &<$model>::new()));

                let mut f = crate::fmt::Formatter;
                assert!(matches!(
                    crate::fmt::Debug::fmt(&m, &mut f),
                    crate::fmt::Result::Ok(())
                ));
            }
        )*};
    }

    variance_marker_tests_not_fstar! {
        test_phantom_covariant_clone_debug: PhantomCovariant<u8>, std::marker::PhantomCovariant<u8>;
        test_phantom_contravariant_clone_debug:
            PhantomContravariant<u8>, std::marker::PhantomContravariant<u8>;
        test_phantom_invariant_clone_debug: PhantomInvariant<u8>, std::marker::PhantomInvariant<u8>;
        test_phantom_covariant_lifetime_clone_debug:
            PhantomCovariantLifetime<'static>, std::marker::PhantomCovariantLifetime<'static>;
        test_phantom_contravariant_lifetime_clone_debug:
            PhantomContravariantLifetime<'static>, std::marker::PhantomContravariantLifetime<'static>;
        test_phantom_invariant_lifetime_clone_debug:
            PhantomInvariantLifetime<'static>, std::marker::PhantomInvariantLifetime<'static>;
    }

    #[test]
    fn test_phantom_pinned() {
        assert_eq!(
            std::mem::size_of::<PhantomPinned>(),
            std::mem::size_of::<std::marker::PhantomPinned>()
        );
        let _: PhantomPinned = crate::default::Default::default();
    }

    // The impls F* lacks or takes from its blanket `Clone` and `Debug` instead.
    // The model's `Formatter` renders nothing, so only success is observable for
    // `Debug`.
    #[cfg(not(hax_backend_fstar))]
    #[test]
    fn test_phantom_pinned_not_fstar() {
        let (m, n): (PhantomPinned, PhantomPinned) =
            (PhantomPinned, crate::default::Default::default());
        let (s, t): (std::marker::PhantomPinned, std::marker::PhantomPinned) =
            (std::marker::PhantomPinned, std::default::Default::default());

        assert_eq!(crate::cmp::PartialEq::eq(&m, &n), s == t);
        assert_eq!(crate::cmp::PartialEq::ne(&m, &n), s != t);
        assert_eq!(
            crate::cmp::PartialOrd::partial_cmp(&m, &n),
            std::cmp::PartialOrd::partial_cmp(&s, &t).inject()
        );
        assert_eq!(
            crate::cmp::Ord::cmp(&m, &n),
            std::cmp::Ord::cmp(&s, &t).inject()
        );

        let mut mh = Log(Vec::new());
        crate::hash::Hash::hash(&m, &mut mh);
        let mut sh = Log(Vec::new());
        std::hash::Hash::hash(&s, &mut sh);
        assert_eq!(mh, sh);

        assert_eq!(
            crate::cmp::PartialEq::ne(&m, &crate::clone::Clone::clone(&m)),
            s != std::clone::Clone::clone(&s)
        );
        let m = crate::clone::Clone::clone_from(m, PhantomPinned);
        assert!(crate::cmp::PartialEq::eq(&m, &PhantomPinned));

        let mut f = crate::fmt::Formatter;
        assert!(matches!(
            crate::fmt::Debug::fmt(&m, &mut f),
            crate::fmt::Result::Ok(())
        ));
    }

    // Pins the model's own deviation: `variance()` goes through `Default`.
    #[test]
    fn test_variance_uses_default() {
        struct Witness(u8);
        #[hax_lib::attributes]
        impl crate::default::Default for Witness {
            fn default() -> Witness {
                Witness(7)
            }
        }
        impl Variance for Witness {}

        assert_eq!(variance::<Witness>().0, 7);
    }
}

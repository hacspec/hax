use crate::prelude::*;
use paste::paste;

macro_rules! mk_aux {
    ($state:ident {$($lts:lifetime)*} $field:ident {$($field_type:tt)+} {$($gen:tt)*} {$($gen_full:tt)*} {$($params:tt)*} {$($fields:tt)*}) => {
        paste ! {
            pub trait [<Has $field:camel>]<$($lts,)*> {
                fn $field(self: &Self) -> $($field_type)+<$($lts)*>;
            }
            impl<$($lts,)*$($gen)*> [<Has $field:camel>]<$($lts,)*> for $state<$($params)*> {
                fn $field(self: &Self) -> $($field_type)+<$($lts)*> {
                    self.$field.clone()
                }
            }
            pub trait [<Has $field:camel Setter>]<$($lts)*> {
                type Out;
                // fn [<with_ $field>]<$($lts,)*$($gen)*>(self: Self, $field: $($field_type)+<$($lts)*>) -> $state<$($params)*>;
                fn [<with_ $field>](self: Self, $field: $($field_type)+<$($lts)*>) -> Self::Out;
            }
            // const _: &str = stringify!(
            #[allow(unused)]
            impl<$($lts,)*$($gen_full)*> [<Has $field:camel Setter>]<$($lts,)*> for $state<$($gen_full)*> {
                type Out = $state<$($params)*>;
                fn [<with_ $field>](self: Self, $field: $($field_type)+<$($lts)*>) -> Self::Out {
                    let __this_field = $field;
                    let $state { $($fields,)* } = self;
                    let $field = __this_field;
                    $state { $($fields,)* }
                }
            }
            // );
            // pub trait [<Has $field:camel Setter>]<$($lts,)*$($gen_full)*> {
            //     fn [<with_ $field>](self: Self, $field: $($field_type)+<$($lts)*>) -> $state<$($params)*>;
            // }
            // impl<$($lts,)*$($gen_full)*> [<Has $field:camel Setter>]<$($lts,)*$($gen_full)*> for $state<$($gen_full)*> {
            //     fn [<with_ $field>](self: Self, $field: $($field_type)+<$($lts)*>) -> $state<$($params)*> {
            //         let __this_field = $field;
            //         let $state { $($fields,)* } = self;
            //         let $field = __this_field;
            //         $state { $($fields,)* }
            //     }
            // }
        }
    };
}
macro_rules! mk_is_state_trait {
    ($lts:tt {$($finished:tt)*} {{$f0:ident, $($l:tt)*} $($f:tt)*} $($generic:tt)*) => {
        paste! {mk_is_state_trait!{
                $lts {$($finished)* [<Has $f0:camel Setter>] <$($l)*> +} {$($f)*} $($generic)*
                // $lts {$($finished)* [<Has $f0:camel Setter>] <$($l)* $($generic)*> +} {$($f)*} $($generic)*
        }}
    };
    ({$($glts:lifetime,)*} {$($finished:tt)*} {} $($generic:tt)*) => {
        pub trait IsState<$($glts,)*> = $($finished)*;
    };
}
macro_rules! mk {
    (struct $state:ident<$($glts:lifetime),*> {$($field:ident : {$($lts:lifetime),*} $field_type:ty),*$(,)?}) => {
        mk!(@$state {} {$($field)*} {$($field: {$($lts),*} {$field_type},)*});
        mk_is_state_trait!({$($glts,)*} {} {$({$field, $($lts,)*})*} $([<$field:camel>],)*);
    };
    (@$state:ident {$($acc:tt)*} $fields:tt {
        $field:ident : $lts:tt $field_type:tt
        $(,$($rest:tt)*)?
    }) => {mk!(@$state {
        $($acc)* $fields $field: $lts $field_type,
    } $fields {$($($rest)*)?} );};
    (@$state:ident $body:tt $fields:tt {$(,)?}) => { mk! (@@ $state $body ); };
    (@@$state:ident {$({$($fields:tt)*} $field:ident : {$($lts:lifetime)*} {$($field_type:tt)+},)*}) => {
        paste! {
            #[derive(Clone)]
            pub struct $state<$([<$field:camel>],)*>{
                $(pub $field: [<$field:camel>],)*
            }
        }
        $(
            macro_rules! __inner_helper {
                ($gen:tt {$$($full_gen:tt)*} {$$($params:tt)*} $field $$($rest:tt)*) => {
                    paste! {__inner_helper!(
                        $gen {$$($full_gen)*[<$field:camel>],}
                        {$$($params)*$($field_type)+<$($lts,)*>,} $$($rest)*
                    );}
                };
                ({$$($gen:tt)*} {$$($full_gen:tt)*} {$$($params:tt)*} $i:ident $$($rest:tt)*) => {
                    paste! {__inner_helper!(
                        {$$($gen)*[<$i:camel>],} {$$($full_gen)*[<$i:camel>],}
                        {$$($params)*[<$i:camel>],} $$($rest)*
                    );}
                };
                ($gen:tt $full_gen:tt $params:tt $$(,)?) => {
                    mk_aux!($state {$($lts)*} $field {$($field_type)+} $gen $full_gen $params {$($fields)*});
                };
            }
            __inner_helper!({} {} {} $($fields)*);
        )*
    };
}

mod types {
    use crate::prelude::*;
    use rustc_middle::ty;
    use std::cell::RefCell;
    use std::collections::HashSet;

    pub struct LocalContextS {
        pub vars: HashMap<rustc_middle::thir::LocalVarId, String>,
    }

    impl Default for LocalContextS {
        fn default() -> Self {
            Self::new()
        }
    }

    impl LocalContextS {
        pub fn new() -> LocalContextS {
            LocalContextS {
                vars: HashMap::new(),
            }
        }
    }

    /// Per-item cache
    pub struct Caches<'tcx> {
        /// Cache the trait resolution engine for each item.
        pub predicate_searcher: crate::traits::PredicateSearcher<'tcx>,
        /// Cache of trait refs to resolved impl expressions.
        pub resolution_cache: HashMap<ty::PolyTraitRef<'tcx>, crate::traits::ImplExpr>,
        /// Cache thir bodies.
        pub thir: Option<(
            Rc<rustc_middle::thir::Thir<'tcx>>,
            rustc_middle::thir::ExprId,
        )>,
    }

    impl<'tcx> Caches<'tcx> {
        pub fn new(tcx: ty::TyCtxt<'tcx>, def_id: RDefId) -> Self {
            Self {
                predicate_searcher: crate::traits::PredicateSearcher::new_for_owner(tcx, def_id),
                resolution_cache: Default::default(),
                thir: Default::default(),
            }
        }
    }

    #[derive(Clone)]
    pub struct Base<'tcx> {
        pub options: Rc<hax_frontend_exporter_options::Options>,
        pub macro_infos: MacroCalls,
        pub local_ctx: Rc<RefCell<LocalContextS>>,
        pub opt_def_id: Option<rustc_hir::def_id::DefId>,
        pub exported_spans: ExportedSpans,
        pub exported_def_ids: ExportedDefIds,
        /// Per-item caches.
        pub caches: Rc<RefCell<HashMap<RDefId, Caches<'tcx>>>>,
        pub tcx: ty::TyCtxt<'tcx>,
        /// Rust doesn't enforce bounds on generic parameters in type
        /// aliases. Thus, when translating type aliases, we need to
        /// disable the resolution of implementation expressions. For
        /// more details, please see
        /// https://github.com/hacspec/hax/issues/707.
        pub ty_alias_mode: bool,
    }

    impl<'tcx> Base<'tcx> {
        pub fn new(
            tcx: rustc_middle::ty::TyCtxt<'tcx>,
            options: hax_frontend_exporter_options::Options,
        ) -> Self {
            Self {
                tcx,
                macro_infos: Rc::new(HashMap::new()),
                caches: Default::default(),
                options: Rc::new(options),
                // Always prefer `s.owner_id()` to `s.base().opt_def_id`.
                // `opt_def_id` is used in `utils` for error reporting
                opt_def_id: None,
                local_ctx: Rc::new(RefCell::new(LocalContextS::new())),
                exported_spans: Rc::new(RefCell::new(HashSet::new())),
                exported_def_ids: Rc::new(RefCell::new(HashSet::new())),
                ty_alias_mode: false,
            }
        }

        /// Access the shared caches. You must not call `sinto` within this function as this will
        /// likely result in `BorrowMut` panics.
        pub fn with_caches<T>(&self, def_id: RDefId, f: impl FnOnce(&mut Caches<'tcx>) -> T) -> T {
            let mut caches = self.caches.borrow_mut();
            let caches_for_def_id = caches
                .entry(def_id)
                .or_insert_with(|| Caches::new(self.tcx, def_id));
            f(caches_for_def_id)
        }
    }

    pub type MacroCalls = Rc<HashMap<Span, Span>>;
    pub type ExportedSpans = Rc<RefCell<HashSet<rustc_span::Span>>>;
    pub type ExportedDefIds = Rc<RefCell<HashSet<rustc_hir::def_id::DefId>>>;
    pub type RcThir<'tcx> = Rc<rustc_middle::thir::Thir<'tcx>>;
    pub type RcMir<'tcx> = Rc<rustc_middle::mir::Body<'tcx>>;
    pub type Binder<'tcx> = rustc_middle::ty::Binder<'tcx, ()>;
}

mk!(
    struct State<'tcx> {
        base: {'tcx} types::Base,
        thir: {'tcx} types::RcThir,
        mir: {'tcx} types::RcMir,
        owner_id: {} rustc_hir::def_id::DefId,
        binder: {'tcx} types::Binder,
    }
);

pub use self::types::*;

pub type StateWithBase<'tcx> = State<Base<'tcx>, (), (), (), ()>;
pub type StateWithOwner<'tcx> = State<Base<'tcx>, (), (), rustc_hir::def_id::DefId, ()>;
pub type StateWithBinder<'tcx> =
    State<Base<'tcx>, (), (), rustc_hir::def_id::DefId, types::Binder<'tcx>>;
pub type StateWithThir<'tcx> =
    State<Base<'tcx>, types::RcThir<'tcx>, (), rustc_hir::def_id::DefId, ()>;
pub type StateWithMir<'tcx> =
    State<Base<'tcx>, (), types::RcMir<'tcx>, rustc_hir::def_id::DefId, ()>;

impl<'tcx> StateWithBase<'tcx> {
    pub fn new(
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
        options: hax_frontend_exporter_options::Options,
    ) -> Self {
        Self {
            thir: (),
            mir: (),
            owner_id: (),
            binder: (),
            base: Base::new(tcx, options),
        }
    }
}

impl<'tcx> StateWithOwner<'tcx> {
    pub fn new_from_state_and_id<S: BaseState<'tcx>>(s: &S, id: rustc_hir::def_id::DefId) -> Self {
        State {
            thir: (),
            mir: (),
            owner_id: id,
            binder: (),
            base: s.base().clone(),
        }
    }
}
impl<'tcx> StateWithMir<'tcx> {
    pub fn new_from_mir(
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
        options: hax_frontend_exporter_options::Options,
        mir: rustc_middle::mir::Body<'tcx>,
        owner_id: rustc_hir::def_id::DefId,
    ) -> Self {
        Self {
            thir: (),
            mir: Rc::new(mir),
            owner_id,
            binder: (),
            base: Base::new(tcx, options),
        }
    }
}
impl<'tcx> StateWithThir<'tcx> {
    pub fn from_thir(
        base: Base<'tcx>,
        owner_id: rustc_hir::def_id::DefId,
        thir: types::RcThir<'tcx>,
    ) -> Self {
        Self {
            thir,
            mir: (),
            owner_id,
            binder: (),
            base,
        }
    }
}

impl<'tcx> StateWithOwner<'tcx> {
    pub fn from_under_owner<S: UnderOwnerState<'tcx>>(s: &S) -> Self {
        Self {
            base: s.base(),
            owner_id: s.owner_id(),
            thir: (),
            mir: (),
            binder: (),
        }
    }
}

/// Updates the OnwerId in a state, making sure to override `opt_def_id` in base as well.
pub fn with_owner_id<THIR, MIR>(
    mut base: types::Base<'_>,
    thir: THIR,
    mir: MIR,
    owner_id: rustc_hir::def_id::DefId,
) -> State<types::Base<'_>, THIR, MIR, rustc_hir::def_id::DefId, ()> {
    base.opt_def_id = Some(owner_id);
    State {
        thir,
        owner_id,
        base,
        mir,
        binder: (),
    }
}

pub trait BaseState<'tcx> = HasBase<'tcx> + Clone + IsState<'tcx>;

/// State of anything below a `owner_id`.
pub trait UnderOwnerState<'tcx> = BaseState<'tcx> + HasOwnerId;

/// State of anything below a binder.
pub trait UnderBinderState<'tcx> = UnderOwnerState<'tcx> + HasBinder<'tcx>;

/// While translating expressions, we expect to always have a THIR
/// body and an `owner_id` in the state
pub trait ExprState<'tcx> = UnderOwnerState<'tcx> + HasThir<'tcx>;

impl ImplInfos {
    fn from(base: Base<'_>, did: rustc_hir::def_id::DefId) -> Self {
        let tcx = base.tcx;
        let s = &with_owner_id(base, (), (), did);

        Self {
            generics: tcx.generics_of(did).sinto(s),
            typ: tcx.type_of(did).instantiate_identity().sinto(s),
            trait_ref: tcx.impl_trait_ref(did).sinto(s),
            clauses: tcx.predicates_defined_on(did).predicates.sinto(s),
        }
    }
}

/// Returns a map from every implementation (`Impl`) `DefId`s to the
/// type they implement, plus the bounds.
pub fn impl_def_ids_to_impled_types_and_bounds<'tcx, S: BaseState<'tcx>>(
    s: &S,
) -> HashMap<DefId, ImplInfos> {
    let Base {
        tcx,
        exported_def_ids,
        ..
    } = s.base();

    let def_ids = exported_def_ids.as_ref().borrow().clone();
    let with_parents = |mut did: rustc_hir::def_id::DefId| {
        let mut acc = vec![did];
        while let Some(parent) = tcx.opt_parent(did) {
            did = parent;
            acc.push(did);
        }
        acc.into_iter()
    };
    use itertools::Itertools;
    def_ids
        .iter()
        .cloned()
        .flat_map(with_parents)
        .unique()
        .filter(|&did| {
            // keep only DefIds that corresponds to implementations
            matches!(
                tcx.def_path(did).data.last(),
                Some(rustc_hir::definitions::DisambiguatedDefPathData {
                    data: rustc_hir::definitions::DefPathData::Impl,
                    ..
                })
            )
        })
        .map(|did| (did.sinto(s), ImplInfos::from(s.base(), did)))
        .collect()
}

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
    use std::cell::RefCell;
    use std::collections::HashSet;

    pub struct LocalContextS {
        pub vars: HashMap<rustc_middle::thir::LocalVarId, String>,
    }

    impl LocalContextS {
        pub fn new() -> LocalContextS {
            LocalContextS {
                vars: HashMap::new(),
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
        pub cached_thirs: Rc<
            HashMap<
                rustc_span::def_id::LocalDefId,
                (
                    Rc<rustc_middle::thir::Thir<'tcx>>,
                    rustc_middle::thir::ExprId,
                ),
            >,
        >,
        pub tcx: rustc_middle::ty::TyCtxt<'tcx>,
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
                cached_thirs: Rc::new(HashMap::new()),
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
    }

    pub type MacroCalls = Rc<HashMap<Span, Span>>;
    pub type ExportedSpans = Rc<RefCell<HashSet<rustc_span::Span>>>;
    pub type ExportedDefIds = Rc<RefCell<HashSet<rustc_hir::def_id::DefId>>>;
    pub type RcThir<'tcx> = Rc<rustc_middle::thir::Thir<'tcx>>;
    pub type RcMir<'tcx> = Rc<rustc_middle::mir::Body<'tcx>>;
}

mk!(
    struct State<'tcx> {
        base: {'tcx} types::Base,
        thir: {'tcx} types::RcThir,
        mir: {'tcx} types::RcMir,
        owner_id: {} rustc_hir::def_id::DefId,
    }
);

pub use types::*;

impl<'tcx> State<Base<'tcx>, (), (), ()> {
    pub fn new(
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
        options: hax_frontend_exporter_options::Options,
    ) -> Self {
        Self {
            thir: (),
            mir: (),
            owner_id: (),
            base: Base::new(tcx, options),
        }
    }
}

impl<'tcx> State<Base<'tcx>, (), (), rustc_hir::def_id::DefId> {
    pub fn new_from_state_and_id<S: BaseState<'tcx>>(s: &S, id: rustc_hir::def_id::DefId) -> Self {
        State {
            thir: (),
            mir: (),
            owner_id: id,
            base: s.base().clone(),
        }
    }
}
impl<'tcx> State<Base<'tcx>, (), Rc<rustc_middle::mir::Body<'tcx>>, rustc_hir::def_id::DefId> {
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
            base: Base::new(tcx, options),
        }
    }
}

/// Updates the OnwerId in a state, making sure to override `opt_def_id` in base as well.
pub fn with_owner_id<'tcx, THIR, MIR>(
    mut base: types::Base<'tcx>,
    thir: THIR,
    mir: MIR,
    owner_id: rustc_hir::def_id::DefId,
) -> State<types::Base<'tcx>, THIR, MIR, rustc_hir::def_id::DefId> {
    base.opt_def_id = Some(owner_id);
    State {
        thir,
        owner_id,
        base,
        mir,
    }
}

pub trait BaseState<'tcx> = HasBase<'tcx> + Clone + IsState<'tcx>;
/// State of anything below a `owner_id`
pub trait UnderOwnerState<'tcx> = BaseState<'tcx> + HasOwnerId;

/// Meta-informations about an `impl<GENERICS[: PREDICATES]> TRAIT for
/// TYPE where PREDICATES {}`
#[derive(Clone, Debug, Serialize, Deserialize, JsonSchema)]
pub struct ImplInfos {
    pub generics: TyGenerics,
    pub clauses: Vec<(Clause, Span)>,
    pub typ: Ty,
    pub trait_ref: Option<TraitRef>,
}

impl ImplInfos {
    fn from<'tcx>(base: Base<'tcx>, did: rustc_hir::def_id::DefId) -> Self {
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
        let mut acc = vec![did.clone()];
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
        .map(with_parents)
        .flatten()
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

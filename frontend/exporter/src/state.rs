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
    use std::collections::{HashMap, HashSet};

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
    }

    impl<'tcx> Base<'tcx> {
        pub fn new(
            tcx: rustc_middle::ty::TyCtxt<'tcx>,
            options: &hax_frontend_exporter_options::Options,
        ) -> Self {
            Self {
                tcx: tcx.clone(),
                macro_infos: Rc::new(HashMap::new()),
                cached_thirs: Rc::new(HashMap::new()),
                options: Rc::new(options.clone()),
                opt_def_id: None,
                local_ctx: Rc::new(RefCell::new(LocalContextS::new())),
                exported_spans: Rc::new(RefCell::new(HashSet::new())),
            }
        }
    }

    pub type MacroCalls = Rc<HashMap<Span, Span>>;
    pub type ExportedSpans = Rc<RefCell<HashSet<rustc_span::Span>>>;
    pub type RcThir<'tcx> = Rc<rustc_middle::thir::Thir<'tcx>>;
    pub type RcMir<'tcx> = Rc<rustc_middle::mir::Body<'tcx>>;
}

mk!(
    struct State<'tcx> {
        base: {'tcx} types::Base,
        thir: {'tcx} types::RcThir,
        mir: {'tcx} types::RcMir,
        owner_id: {} rustc_hir::hir_id::OwnerId,
    }
);

pub use types::*;

impl<'tcx> State<Base<'tcx>, (), (), ()> {
    pub fn new(
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
        options: &hax_frontend_exporter_options::Options,
    ) -> Self {
        Self {
            thir: (),
            mir: (),
            owner_id: (),
            base: Base::new(tcx, options),
        }
    }
}

pub trait BaseState<'tcx> = HasBase<'tcx> + Clone + IsState<'tcx>;

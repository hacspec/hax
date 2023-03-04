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

pub mod types {
    use std::cell::RefCell;
    use std::collections::HashMap;
    use std::rc::Rc;
    pub type LocalIdentMap = Rc<RefCell<HashMap<rustc_middle::thir::LocalVarId, String>>>;
    pub type MacroCalls = Box<HashMap<rustc_span::Span, rustc_ast::ast::MacCall>>;
    pub type Options = Box<crate::options::Options>;
    pub type OptDefId = Option<rustc_hir::def_id::DefId>;
    // pub type Predicates<'tcx> = Box<rustc_middle::ty::List<rustc_middle::ty::Predicate<'tcx>>>;
}

mk!(
    struct State<'tcx> {
        tcx: {'tcx} rustc_middle::ty::TyCtxt,
        options: {} types::Options,
        thir: {'tcx} rustc_middle::thir::Thir,
        def_id: {} rustc_hir::def_id::DefId,
        opt_def_id: {} types::OptDefId,
        macro_infos: {} types::MacroCalls,
        local_ident_map: {} types::LocalIdentMap,
    }
);

// trait IsStateX {
//     type TCX;
//     type OPTIONS;
//     type THIR;
//     type DEF_ID;
//     type MACRO_INFOS;
//     type LOCAL_IDENT_MAP;

//     fn tcx();
// }

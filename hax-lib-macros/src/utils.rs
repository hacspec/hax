use crate::prelude::*;
use crate::rewrite_self::*;

pub trait BlockExt {
    fn make_quantifiers_available(&mut self);
}

impl BlockExt for Block {
    fn make_quantifiers_available(&mut self) {
        // self.stmts.insert(0, parse_quote! {#HaxQuantifiers});
        self.stmts.insert(
            0,
            Stmt::Item(Item::Verbatim(HaxQuantifiers.to_token_stream())),
        );
    }
}

pub struct HaxQuantifiers;
impl ToTokens for HaxQuantifiers {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let status_attr = &AttrPayload::ItemStatus(ItemStatus::Included { late_skip: true });
        quote! {
            #AttrHaxLang
            #status_attr
            fn forall<T, F: Fn(T) -> bool>(f: F) -> bool {
                true
            }
            #AttrHaxLang
            #status_attr
            fn exists<T, F: Fn(T) -> bool>(f: F) -> bool {
                true
            }
        }
        .to_tokens(tokens)
    }
}

pub enum FnDecorationKind {
    Requires,
    Ensures { ret_binder: Pat },
    Decreases,
}

impl ToString for FnDecorationKind {
    fn to_string(&self) -> String {
        match self {
            FnDecorationKind::Requires => "requires".to_string(),
            FnDecorationKind::Ensures { .. } => "ensures".to_string(),
            FnDecorationKind::Decreases { .. } => "decreases".to_string(),
        }
    }
}

impl From<FnDecorationKind> for AssociationRole {
    fn from(kind: FnDecorationKind) -> Self {
        match &kind {
            FnDecorationKind::Requires => AssociationRole::Requires,
            FnDecorationKind::Ensures { .. } => AssociationRole::Ensures,
            FnDecorationKind::Decreases => AssociationRole::Decreases,
        }
    }
}

fn merge_generics(x: Generics, y: Generics) -> Generics {
    Generics {
        lt_token: x.lt_token.or(y.lt_token),
        gt_token: x.gt_token.or(y.gt_token),
        params: {
            let lts = x
                .lifetimes()
                .chain(y.lifetimes())
                .cloned()
                .map(GenericParam::Lifetime);
            let not_lts = x
                .params
                .clone()
                .into_iter()
                .filter(|p| !matches!(p, GenericParam::Lifetime(_)))
                .chain(
                    y.params
                        .clone()
                        .into_iter()
                        .filter(|p| !matches!(p, GenericParam::Lifetime(_))),
                );
            lts.chain(not_lts).collect()
        },
        where_clause: match (x.where_clause, y.where_clause) {
            (Some(wx), Some(wy)) => Some(syn::WhereClause {
                where_token: wx.where_token,
                predicates: wx
                    .predicates
                    .into_iter()
                    .chain(wy.predicates.into_iter())
                    .collect(),
            }),
            (Some(w), None) | (None, Some(w)) => Some(w),
            (None, None) => None,
        },
    }
}

fn drop_mut_ref(sig: &mut Signature) -> bool {
    let mut any_mut_ref = false;
    for input in &mut sig.inputs {
        if let FnArg::Receiver(syn::Receiver {
            reference: Some(_),
            mutability,
            ..
        })
        | FnArg::Typed(syn::PatType {
            ty: box syn::Type::Reference(syn::TypeReference { mutability, .. }),
            ..
        }) = input
        {
            any_mut_ref |= mutability.is_some();
            *mutability = None;
        }
    }
    any_mut_ref
}

pub fn make_fn_decoration(
    mut phi: Expr,
    mut signature: Signature,
    kind: FnDecorationKind,
    generics: Option<Generics>,
    self_type: Option<Type>,
) -> (TokenStream, AttrPayload) {
    let uid = ItemUid::fresh();
    let any_mut_ref = drop_mut_ref(&mut signature);
    if any_mut_ref && let FnDecorationKind::Ensures { .. } = kind {
        panic!("For now, ensures clause don't work on funciton that have `&mut` inputs (see https://github.com/hacspec/hacspec-v2/issues/290)")
    }

    let self_ident: Ident = syn::parse_quote! {self_};
    let mut rewriter = RewriteSelf::new(self_ident, self_type);
    rewriter.visit_expr_mut(&mut phi);
    let decoration = {
        let decoration_sig = {
            let mut sig = signature;
            rewriter.visit_signature_mut(&mut sig);
            sig.ident = format_ident!("{}", kind.to_string());
            if let FnDecorationKind::Ensures { ret_binder } = &kind {
                let output = match sig.output {
                    syn::ReturnType::Default => quote! {()},
                    syn::ReturnType::Type(_, t) => quote! {#t},
                };
                sig.inputs.push(syn::parse_quote! {#ret_binder: #output});
            }
            if let Some(generics) = generics {
                sig.generics = merge_generics(generics, sig.generics);
            }
            sig.output = if let FnDecorationKind::Decreases = &kind {
                syn::parse_quote! { -> Box<dyn Any> }
            } else {
                syn::parse_quote! { -> bool }
            };
            sig
        };
        let uid_attr = AttrPayload::Uid(uid.clone());
        let late_skip = &AttrPayload::ItemStatus(ItemStatus::Included { late_skip: true });
        let any_trait = if let FnDecorationKind::Decreases = &kind {
            phi = parse_quote! {Box::new(#phi)};
            quote! {#AttrHaxLang #[allow(unused)] trait Any {} impl<T> Any for T {}}
        } else {
            quote! {}
        };
        let quantifiers = if let FnDecorationKind::Decreases = &kind {
            None
        } else {
            Some(HaxQuantifiers)
        };
        let future = if let FnDecorationKind::Ensures { .. } = &kind {
            quote! { #late_skip #AttrHaxLang fn future<T>(x: &mut T) -> &T { x } }
        } else {
            quote! {}
        };
        quote! {
            #late_skip
            const _: () = {
                #quantifiers
                #any_trait
                #future
                #uid_attr
                #late_skip
                #[allow(unused)]
                #decoration_sig {
                    #phi
                }
            };
        }
    };

    let assoc_attr = AttrPayload::AssociatedItem {
        role: kind.into(),
        item: uid,
    };
    (decoration, assoc_attr)
}

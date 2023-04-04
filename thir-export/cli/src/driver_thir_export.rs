#![feature(rustc_private)]
#![feature(box_syntax)]
#![feature(box_patterns)]
#![feature(concat_idents)]
#![feature(trait_alias)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unreachable_code)]
#![allow(dead_code)]
#![feature(macro_metavar_expr)]

extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_hir_analysis;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_lint;
extern crate rustc_lint_defs;
extern crate rustc_middle;
extern crate rustc_mir_build;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_type_ir;

use rustc_ast::ast;
use rustc_data_structures::sync::Lrc;
use rustc_driver::{Callbacks, Compilation};
use rustc_errors::DiagnosticId;
use rustc_hir::hir_id::HirId;
use rustc_interface::{interface::Compiler, Queries};
use rustc_lint::{EarlyContext, EarlyLintPass, LateContext, LateLintPass, LintPass};
use rustc_lint_defs::{declare_lint, declare_lint_pass};
use rustc_middle::middle::region::Scope;
use rustc_session::Session;

use rustc_middle::ty::TyCtxt;
use rustc_middle::{
    thir,
    thir::{Block, BlockId, Expr, ExprId, ExprKind, Pat, PatKind, Stmt, StmtId, StmtKind, Thir},
};
// mod thir_ast;

// mod translate;
// #[macro_use]
// mod sinto;
// use sinto::*;
// mod items_ast;
// mod options;
// use options::Options;

use thir_export::{self, LifetimeParamKind, TraitItem, TraitItemKind, WherePredicate};

use std::cell::RefCell;
use std::path;
use std::rc::Rc;

fn browse_items<'tcx>(
    options: &thir_export::Options,
    macro_calls: HashMap<rustc_span::Span, rustc_ast::ast::MacCall>,
    tcx: TyCtxt<'tcx>,
    session: &Lrc<Session>,
) {
    let hir = tcx.hir();
    let bodies = hir.body_owners();

    // Register linter
    {
        use rustc_hir::{intravisit::*, *};
        use rustc_middle::hir::nested_filter::OnlyBodies;
        use rustc_span::{symbol::Ident, Span};

        struct HirLinter<'a, 'tcx> {
            session: &'a Lrc<Session>,
            tcx: &'a TyCtxt<'tcx>,
            derive_allow_list: Vec<String>,
            trait_block_list: Vec<String>,
        }

        fn has_attr(attrs: &[ast::Attribute], symbol: Symbol) -> bool {
            attrs.iter().any(|attr| attr.has_name(symbol))
        }

        macro_rules! skip_derived {
            ($self:ident, $hir_id:expr) => {
                if $self.any_parent_is_automatically_derived($hir_id) {
                    log::trace!("   skipping automatically derived code");
                    return;
                }
            };
        }

        impl<'a, 'v> HirLinter<'a, 'v> {
            fn any_parent_has_attr(&self, hir_id: HirId, symbol: Symbol) -> bool {
                let map = &self.tcx.hir();
                let mut prev_enclosing_node = None;
                let mut enclosing_node = hir_id;
                while Some(enclosing_node) != prev_enclosing_node {
                    if has_attr(map.attrs(enclosing_node), symbol) {
                        return true;
                    }
                    prev_enclosing_node = Some(enclosing_node);
                    enclosing_node = map.get_parent_item(enclosing_node).into();
                }

                false
            }

            fn any_parent_is_automatically_derived(&self, hir_id: HirId) -> bool {
                self.any_parent_has_attr(hir_id, rustc_span::symbol::sym::automatically_derived)
            }

            fn explicit_lifetime(&self, span: Span) {
                self.session.span_warn_with_code(
                    span,
                    "[Circus] Explicit lifetimes are not supported",
                    DiagnosticId::Lint {
                        name: "Lifetime".to_string(),
                        has_future_breakage: false,
                        is_force_warn: true,
                    },
                );
            }

            fn mut_borrow_let(&self, span: Span) {
                self.session.span_warn_with_code(
                    span,
                    "[Circus] Mutable borrows are not supported",
                    DiagnosticId::Lint {
                        name: "Mut borrow".to_string(),
                        has_future_breakage: false,
                        is_force_warn: true,
                    },
                );
            }

            fn extern_crate(&self, span: Span) {
                self.session.span_warn_with_code(
                    span,
                    "[Circus] External items need a model",
                    DiagnosticId::Lint {
                        name: "External".to_string(),
                        has_future_breakage: false,
                        is_force_warn: true,
                    },
                );
            }

            fn no_trait_objects(&self, span: Span) {
                self.session.span_warn_with_code(
                    span,
                    "[Circus] Trait objects are not supported",
                    DiagnosticId::Lint {
                        name: "Trait objects".to_string(),
                        has_future_breakage: false,
                        is_force_warn: true,
                    },
                );
            }

            fn no_mut_self(&self, span: Span) {
                self.session.span_warn_with_code(
                    span,
                    "[Circus] Mutable self is not supported",
                    DiagnosticId::Lint {
                        name: "Mutable self".to_string(),
                        has_future_breakage: false,
                        is_force_warn: true,
                    },
                );
            }

            fn no_assoc_items(&self, span: Span) {
                self.session.span_warn_with_code(
                    span,
                    "[Circus] Associated items are not supported",
                    DiagnosticId::Lint {
                        name: "Assoc items".to_string(),
                        has_future_breakage: false,
                        is_force_warn: true,
                    },
                );
            }

            fn unsupported_item(&self, span: Span, ident: String) {
                self.session.span_warn_with_code(
                    span,
                    format!("[Circus] {ident:?} is not supported"),
                    DiagnosticId::Lint {
                        name: "Unsupported item".to_string(),
                        has_future_breakage: false,
                        is_force_warn: true,
                    },
                );
            }

            fn no_fn_mut(&self, span: Span) {
                self.session.span_warn_with_code(
                    span,
                    "[Circus] FnMut is not supported",
                    DiagnosticId::Lint {
                        name: "Where".to_string(),
                        has_future_breakage: false,
                        is_force_warn: true,
                    },
                );
            }

            fn no_where_predicate(&self, span: Span) {
                self.session.span_warn_with_code(
                    span,
                    "[Circus] Where predicates are not supported",
                    DiagnosticId::Lint {
                        name: "Where".to_string(),
                        has_future_breakage: false,
                        is_force_warn: true,
                    },
                );
            }

            fn no_async_await(&self, span: Span) {
                self.session.span_warn_with_code(
                    span,
                    "[Circus] Async and await are not supported",
                    DiagnosticId::Lint {
                        name: "Async".to_string(),
                        has_future_breakage: false,
                        is_force_warn: true,
                    },
                );
            }

            fn no_unsafe(&self, span: Span) {
                self.session.span_warn_with_code(
                    span,
                    "[Circus] Unsafe code is not supported",
                    DiagnosticId::Lint {
                        name: "Unsafe".to_string(),
                        has_future_breakage: false,
                        is_force_warn: true,
                    },
                );
            }

            fn unsupported_loop(&self, span: Span) {
                self.session.span_warn_with_code(
                    span,
                    "[Circus] loop and while are not supported",
                    DiagnosticId::Lint {
                        name: "Loops".to_string(),
                        has_future_breakage: false,
                        is_force_warn: true,
                    },
                );
            }

            fn no_union(&self, span: Span) {
                self.session.span_warn_with_code(
                    span,
                    "[Circus] Unions are not supported",
                    DiagnosticId::Lint {
                        name: "Unsupported item".to_string(),
                        has_future_breakage: false,
                        is_force_warn: true,
                    },
                );
            }

            fn derive_external_trait(&self, span: Span, trait_name: String) {
                self.session.span_warn_with_code(
                    span,
                    format!(
                        "[Circus] Implementation of external trait {trait_name} will require a model"
                    ),
                    DiagnosticId::Lint {
                        name: "External trait".to_string(),
                        has_future_breakage: false,
                        is_force_warn: true,
                    },
                );
            }

            fn foreign_items(&self, key: rustc_span::def_id::DefId, span: Span) {
                // Check for foreign item
                if self.tcx.is_foreign_item(key) {
                    log::trace!("foreign item: {:#?}", span);
                }
            }
        }

        impl<'v, 'a> Visitor<'v> for HirLinter<'a, 'v> {
            type NestedFilter = OnlyBodies;

            fn nested_visit_map(&mut self) -> Self::Map {
                log::trace!(" >>> visiting nested map");
                self.tcx.hir()
            }

            fn visit_nested_trait_item(&mut self, id: TraitItemId) {
                log::trace!(" >>> visiting nested trait item");

                walk_trait_item(self, self.tcx.hir().trait_item(id));
            }
            fn visit_nested_impl_item(&mut self, id: ImplItemId) {
                log::trace!(" >>> visiting nested impl item");

                walk_impl_item(self, self.tcx.hir().impl_item(id));
            }
            fn visit_nested_foreign_item(&mut self, id: ForeignItemId) {
                log::trace!(" >>> visiting nested foreign item");
            }
            fn visit_nested_body(&mut self, id: BodyId) {
                log::trace!(" >>> visiting nested body");

                walk_body(self, self.tcx.hir().body(id));
            }

            fn visit_item(&mut self, i: &'v Item<'v>) {
                log::trace!("visiting item {:?} at {:?}", i.ident.name, i.span);
                skip_derived!(self, i.hir_id());
                // log::trace!("   item kind: {:#?}", i.kind);

                match i.kind {
                    ItemKind::Union(_, _) => {
                        // TODO: This should be an error (span_err_with_code)
                        self.no_union(i.span)
                    }
                    ItemKind::GlobalAsm(_) => self.no_unsafe(i.span),
                    ItemKind::Impl(imp) => {
                        // log::trace!("     impl {:?}", imp.self_ty.kind);
                        if imp.unsafety == Unsafety::Unsafe {
                            self.no_unsafe(imp.items[0].span); // TODO: What's the right span?
                        }
                        if let Some(of_trait) = &imp.of_trait {
                            // XXX: We probably want to get this in. Only look for external functions.
                            let def_id = of_trait.hir_ref_id.owner.def_id.to_def_id();
                            if self
                                .tcx
                                .has_attr(def_id, rustc_span::symbol::sym::automatically_derived)
                            {
                                let path_string = of_trait
                                    .path
                                    .segments
                                    .iter()
                                    .map(|seg| seg.ident.as_str())
                                    .collect::<Vec<&str>>()
                                    .join("::");
                                let crate_path = of_trait
                                    .path
                                    .segments
                                    .first()
                                    .unwrap() // XXX: Is this safe?
                                    .ident
                                    .as_str()
                                    .to_string();
                                if self.derive_allow_list.contains(&crate_path)
                                    || self.derive_allow_list.contains(&path_string)
                                {
                                    // We don't want to go into derived items.
                                    log::trace!("   Skipping trait implementation of allowlist");
                                    return;
                                } else {
                                    let path_string = match path_string.split_once(':') {
                                        Some((left, right)) => right[1..].to_string(),
                                        None => path_string,
                                    };
                                    self.derive_external_trait(i.span, path_string);

                                    // Don't go any further
                                    return;
                                }
                            }
                        }
                    }
                    _ => (),
                }

                // Check for foreign item
                self.foreign_items(i.owner_id.def_id.to_def_id(), i.span);

                // keep going
                walk_item(self, i);
            }
            fn visit_body(&mut self, b: &'v Body<'v>) {
                log::trace!(" >>> visiting body");

                // keep going
                walk_body(self, b);
            }

            ///////////////

            fn visit_id(&mut self, hir_id: HirId) {
                log::trace!(
                    "visiting id {hir_id:?} from def path {:?}",
                    self.tcx.def_path(hir_id.owner.to_def_id())
                );
                // log::trace!(
                //     "visiting id at {:?} with node {:?}",
                //     self.tcx.hir().span_if_local(hir_id.owner.to_def_id()),
                //     self.tcx.hir().find(hir_id)
                // );
                // log::trace!(
                //     "visiting id at {:?} is foreign: {:?}",
                //     self.tcx.hir().span_if_local(hir_id.owner.to_def_id()),
                //     self.tcx.is_foreign_item(hir_id.owner)
                // );
                // Nothing to do.
            }
            fn visit_name(&mut self, name: Symbol) {
                log::trace!("visiting name {:?}", name);
                // Nothing to do.
            }
            fn visit_ident(&mut self, ident: Ident) {
                log::trace!(" >>> visiting ident {:?}", ident);

                // XXX: This really shouldn't be done here but earlier.
                if ident.name.as_str() == "FnMut" {
                    self.no_fn_mut(ident.span);
                    return;
                }

                walk_ident(self, ident)
            }
            fn visit_mod(&mut self, m: &'v Mod<'v>, s: Span, n: HirId) {
                log::trace!(" >>> visiting mod {:?}", s);

                // keep going
                walk_mod(self, m, n);
            }
            fn visit_foreign_item(&mut self, i: &'v ForeignItem<'v>) {
                log::trace!("visiting foreign item {:?} at {:?}", i.ident, i.span);
                walk_foreign_item(self, i)
            }
            fn visit_local(&mut self, l: &'v Local<'v>) {
                log::trace!(" >>> visiting local {:?}", l.span);
                walk_local(self, l)
            }
            fn visit_block(&mut self, b: &'v Block<'v>) {
                log::trace!(" >>> visiting block {:?}", b.span);
                walk_block(self, b)
            }
            fn visit_stmt(&mut self, s: &'v Stmt<'v>) {
                log::trace!(
                    " >>> visiting stmt {:?} at {:?}",
                    self.tcx.opt_item_name(s.hir_id.owner.to_def_id()).unwrap(),
                    s.span
                );

                match &s.kind {
                    StmtKind::Local(b) => {
                        // log::trace!("       local stmt");
                        if let Some(init) = b.init {
                            match init.kind {
                                ExprKind::AddrOf(x, f, s) => {
                                    // Don't allow raw borrows (pointer) and mutable borrows.
                                    if matches!(x, BorrowKind::Raw) || matches!(f, Mutability::Mut)
                                    {
                                        self.mut_borrow_let(b.span)
                                    }
                                }
                                _ => (),
                            }
                        }
                        if let Some(els) = b.els {}
                    }
                    StmtKind::Item(_) => (), // log::trace!("       item stmt"),
                    StmtKind::Expr(_) => (), // log::trace!("       expr stmt"),
                    StmtKind::Semi(_) => (), // log::trace!("       semi stmt"),
                }

                // keep going
                walk_stmt(self, s);
            }
            fn visit_arm(&mut self, a: &'v Arm<'v>) {
                log::trace!(" >>> visiting arm {:?}", a.span);
                walk_arm(self, a)
            }
            fn visit_pat(&mut self, p: &'v Pat<'v>) {
                log::trace!(" >>> visiting pat {:?}", p.span);
                walk_pat(self, p)
            }
            fn visit_pat_field(&mut self, f: &'v PatField<'v>) {
                log::trace!(" >>> visiting pat field {:?} at {:?}", f.ident, f.span);
                walk_pat_field(self, f)
            }
            fn visit_array_length(&mut self, len: &'v ArrayLen) {
                log::trace!(" >>> visiting array length");
                walk_array_len(self, len)
            }
            fn visit_anon_const(&mut self, c: &'v AnonConst) {
                log::trace!(" >>> visiting anon const");
                walk_anon_const(self, c)
            }
            fn visit_expr(&mut self, ex: &'v Expr<'v>) {
                log::trace!("visiting expr {:?}", ex.span);
                skip_derived!(self, ex.hir_id);
                // log::trace!("   Node: {:#?}", self.tcx.hir().find(ex.hir_id));

                match &ex.kind {
                    ExprKind::Block(block, _) => match block.rules {
                        BlockCheckMode::UnsafeBlock(UnsafeSource::UserProvided) => {
                            self.no_unsafe(block.span)
                        }
                        _ => (),
                    },
                    ExprKind::Loop(block, label, source, span) => match source {
                        LoopSource::Loop | LoopSource::While => self.unsupported_loop(*span),
                        LoopSource::ForLoop => log::trace!(" >>> hir for loop"),
                    },
                    // FIXME: where to get this from?
                    // ExprKind::Async(e, c, b) => self.no_async_await(b.span),
                    // ExprKind::Await(a) => self.no_async_await(a.span),
                    ExprKind::InlineAsm(p) => self.no_unsafe(p.line_spans[0]),
                    ExprKind::Call(expr, exprs) => {
                        // log::trace!("call: {:#?}", expr);
                        if self.tcx.is_foreign_item(expr.hir_id.owner.def_id) {
                            log::trace!("foreign call: {:#?}", expr.span);
                        }
                    }
                    ExprKind::MethodCall(path, expr, exprs, span) => {
                        // log::trace!("method call: {:#?}", path);
                        if self.tcx.is_foreign_item(expr.hir_id.owner.def_id) {
                            log::trace!("foreign method call: {:#?}", expr.span);
                        }
                    }
                    ExprKind::Path(qpath) => {
                        match qpath {
                            QPath::Resolved(_, path) => match path.res {
                                def::Res::Def(_def_kind, def_id) => {
                                    if !def_id.is_local() {
                                        log::trace!("   non local path at: {:?}", path.span);

                                        let path_string = path
                                            .segments
                                            .iter()
                                            .map(|seg| seg.ident.as_str())
                                            .collect::<Vec<&str>>()
                                            .join("::");

                                        let crate_path = path
                                            .segments
                                            .first()
                                            .unwrap() // XXX: Is this safe?
                                            .ident
                                            .as_str()
                                            .to_string();

                                        log::trace!("   path: {path_string:?}");
                                        log::trace!("   crate: {crate_path:?}");

                                        if self.derive_allow_list.contains(&crate_path)
                                            || self.derive_allow_list.contains(&path_string)
                                        {
                                            log::trace!(
                                                "   We skip trait implementation of allowlist?"
                                            );
                                        } else {
                                            // FIXME
                                            // self.extern_crate(path.span);
                                        }
                                        return;
                                    }
                                }
                                _ => (),
                            },
                            _ => (),
                        }
                    }
                    _ => (), // log::trace!("found expression {:?} at {:?}", ex.kind, ex.span),
                }

                // keep going
                walk_expr(self, ex);
            }
            fn visit_let_expr(&mut self, lex: &'v Let<'v>) {
                log::trace!(" >>> visiting let expr {:?}", lex.span);
                walk_let_expr(self, lex)
            }
            fn visit_expr_field(&mut self, field: &'v ExprField<'v>) {
                log::trace!(" >>> visiting expr field {:?}", field.ident);
                walk_expr_field(self, field)
            }
            fn visit_ty(&mut self, t: &'v Ty<'v>) {
                log::trace!(" >>> visiting ty {:?}", t.span);
                walk_ty(self, t)
            }
            fn visit_generic_param(&mut self, p: &'v GenericParam<'v>) {
                log::trace!("visiting generic param {:?}", p.span);
                log::trace!("   name: {:?}", p.name);

                walk_generic_param(self, p)
            }
            fn visit_const_param_default(&mut self, _param: HirId, ct: &'v AnonConst) {
                log::trace!(" >>> visiting const param default");
                walk_const_param_default(self, ct)
            }
            fn visit_generics(&mut self, g: &'v Generics<'v>) {
                log::trace!("visiting generics {:?}", g.span);
                walk_generics(self, g)
            }
            fn visit_where_predicate(&mut self, predicate: &'v WherePredicate<'v>) {
                log::trace!("visiting where predicate");

                match predicate {
                    WherePredicate::BoundPredicate(p) => {
                        // log::trace!("   bound predicate {:#?}", p.bounds);
                        for bound in p.bounds {
                            match bound {
                                GenericBound::LangItemTrait(
                                    lang_item,
                                    span,
                                    hir_id,
                                    generic_args,
                                ) => {
                                    // XXX: for some reason FnMut is not a lang item
                                    log::trace!("  lang trait bound {:?}", span);
                                    if matches!(lang_item, LangItem::FnMut) {
                                        self.no_fn_mut(*span);
                                    }
                                }
                                GenericBound::Trait(trait_ref, bound_modifier) => {
                                    log::trace!("  trait bound {:?}", trait_ref);
                                    // log::trace!(
                                    //     "  node {:#?}",
                                    //     self.tcx.hir().get(trait_ref.trait_ref.hir_ref_id)
                                    // );
                                }
                                _ => (),
                            }
                        }
                    }
                    WherePredicate::RegionPredicate(p) => self.explicit_lifetime(p.span),
                    WherePredicate::EqPredicate(p) => {
                        log::trace!("   eq predicate {:?}/{:?}", p.lhs_ty, p.rhs_ty);
                    }
                }

                // keep going
                walk_where_predicate(self, predicate);
            }
            fn visit_fn_ret_ty(&mut self, ret_ty: &'v FnRetTy<'v>) {
                log::trace!(" >>> visiting fn ret ty");
                walk_fn_ret_ty(self, ret_ty)
            }
            fn visit_fn_decl(&mut self, fd: &'v FnDecl<'v>) {
                log::trace!(" >>> visiting fn decl");
                walk_fn_decl(self, fd)
            }
            fn visit_fn(
                &mut self,
                fk: FnKind<'v>,
                fd: &'v FnDecl<'v>,
                b: BodyId,
                span: Span,
                id: HirId,
            ) {
                log::trace!(" >>> visiting fn at {:?}", span);
                skip_derived!(self, id);

                fn check_ty_kind(visitor: &HirLinter, k: &TyKind, span: Span) {
                    match k {
                        TyKind::Ptr(_) => visitor.no_unsafe(span),
                        TyKind::TraitObject(_, _, _) => {
                            visitor.no_trait_objects(span);
                        }
                        TyKind::Rptr(lifetime, ty) => {
                            // TODO: check lifetime. only allow anonymous
                            log::trace!("   lifetime {:?}", lifetime.ident);
                            // log::trace!("   ref ty {:#?}", ty);

                            // check for mutable self.
                            // we have to do that here, because we know it's mut here.
                            if matches!(ty.mutbl, Mutability::Mut) {
                                match &ty.ty.kind {
                                    TyKind::Path(path) => match path {
                                        QPath::Resolved(ty, p) => {
                                            if p.segments[0].ident.as_str() == "Self" {
                                                visitor.no_mut_self(p.span)
                                            }
                                        }
                                        _ => (),
                                    },
                                    _ => (),
                                }
                            }

                            check_ty_kind(visitor, &ty.ty.kind, span)
                        }
                        TyKind::OpaqueDef(_, _, _) => {
                            visitor.no_trait_objects(span);
                        }
                        TyKind::Path(path) => match path {
                            QPath::Resolved(ty, p) => {
                                if let Some(ty) = ty {
                                    check_ty_kind(visitor, &ty.kind, span)
                                }

                                // check for trait objects (impl in the path)
                                if p.segments
                                    .iter()
                                    .any(|s| s.ident.to_string().contains("impl"))
                                {
                                    visitor.no_trait_objects(span);
                                }
                            }
                            QPath::TypeRelative(ty, p) => check_ty_kind(visitor, &ty.kind, span),
                            QPath::LangItem(lang_item, span, hir_id) => (),
                        },
                        _ => (),
                    }
                }

                match fk {
                    FnKind::ItemFn(ident, generics, header) => {
                        log::trace!("   ItemFn: {:?}", ident);
                        // TODO: All this should be an error (span_err_with_code)
                        // Unsafe functions
                        if header.unsafety == Unsafety::Unsafe {
                            self.no_unsafe(span);
                        }

                        // async functions
                        if header.asyncness == IsAsync::Async {
                            self.no_async_await(span);
                        }

                        // Check generics for lifetimes
                        for predicate in generics.predicates {
                            match &predicate {
                                WherePredicate::RegionPredicate(region) => {
                                    self.explicit_lifetime(region.span)
                                }
                                WherePredicate::BoundPredicate(bound) => {
                                    for bound in bound.bounds {
                                        match bound {
                                            GenericBound::Trait(poly_ref, modifier) => {
                                                let path_string = poly_ref
                                                    .trait_ref
                                                    .path
                                                    .segments
                                                    .iter()
                                                    .map(|seg| seg.ident.as_str())
                                                    .collect::<Vec<&str>>()
                                                    .join("::");
                                                log::trace!(
                                                    "   trait implementation of {:?}",
                                                    path_string
                                                );

                                                if self.trait_block_list.contains(&path_string) {
                                                    self.unsupported_item(
                                                        poly_ref.span,
                                                        path_string,
                                                    );
                                                }
                                            }
                                            _ => (),
                                        }
                                    }
                                }
                                _ => (),
                            }
                        }
                        for param in generics.params {
                            match param.kind {
                                GenericParamKind::Lifetime { kind } => match kind {
                                    LifetimeParamKind::Explicit => {
                                        self.explicit_lifetime(param.span)
                                    }
                                    _ => (),
                                },
                                _ => (),
                            }
                        }
                    }
                    FnKind::Method(ident, sig) => {
                        log::trace!("   Method: {:?}", ident);
                        // TODO: All this should be an error (span_err_with_code)
                        // Unsafe functions
                        if sig.header.unsafety == Unsafety::Unsafe {
                            self.no_unsafe(span);
                        }

                        // async functions
                        if sig.header.asyncness == IsAsync::Async {
                            self.no_async_await(span);
                        }

                        // Check method input arguments
                        for input in sig.decl.inputs {
                            check_ty_kind(self, &input.kind, input.span);
                        }
                    }
                    FnKind::Closure => (),
                }
                fd.inputs.iter().for_each(|param| {
                    // // No dyn/trait object
                    // FIXME
                    // log::trace!(" >>> fd inputs {:#?}", param);
                    check_ty_kind(self, &param.kind, param.span);
                });

                // keep going
                walk_fn(self, fk, fd, b, id);
            }
            fn visit_use(&mut self, path: &'v UsePath<'v>, hir_id: HirId) {
                // FIXME
                log::trace!(" >>> visiting use {:?}", path.span);

                // keep going
                walk_use(self, path, hir_id);
            }
            fn visit_trait_item(&mut self, ti: &'v TraitItem<'v>) {
                log::trace!(
                    " >>> visiting trait item {:?} at {:?}",
                    ti.ident.name,
                    ti.span
                );
                skip_derived!(self, ti.hir_id());

                // match &ti.kind {
                //     TraitItemKind::Const(_, _) => self.no_assoc_items(ti.span),
                //     TraitItemKind::Type(_, _) => self.no_assoc_items(ti.span),
                //     TraitItemKind::Fn(bounds, ty) => (),
                // }

                // keep going
                walk_trait_item(self, ti);
            }
            fn visit_trait_item_ref(&mut self, ii: &'v TraitItemRef) {
                log::trace!(
                    " >>> visiting trait item ref {:?} at {:?}",
                    ii.ident,
                    ii.span
                );
                walk_trait_item_ref(self, ii)
            }
            fn visit_impl_item(&mut self, ii: &'v ImplItem<'v>) {
                log::trace!("visiting impl item {:?} at {:?}", ii.ident.name, ii.span,);
                skip_derived!(self, ii.hir_id());

                // log::trace!("   item: {:#?}", ii);

                // Check the trait for this item.
                for predicate in ii.generics.predicates {
                    match predicate {
                        WherePredicate::BoundPredicate(bound) => {
                            for bound in bound.bounds {
                                match bound {
                                    GenericBound::Trait(poly_ref, modifier) => {
                                        let path_string = poly_ref
                                            .trait_ref
                                            .path
                                            .segments
                                            .iter()
                                            .map(|seg| seg.ident.as_str())
                                            .collect::<Vec<&str>>()
                                            .join("::");

                                        let crate_path = poly_ref
                                            .trait_ref
                                            .path
                                            .segments
                                            .first()
                                            .unwrap() // XXX: Is this safe?
                                            .ident
                                            .as_str()
                                            .to_string();
                                        if !self.derive_allow_list.contains(&crate_path)
                                            && !self.derive_allow_list.contains(&path_string)
                                        {
                                            // We don't want to go into these derived items
                                            // when they are on the allow list.
                                            log::trace!(
                                                "    found trait impl for trait {:?}",
                                                path_string
                                            );
                                            log::trace!(
                                                "   Skipping trait implementation of allowlist"
                                            );
                                            return;
                                        }
                                    }
                                    _ => (),
                                }
                            }
                        }
                        _ => (),
                    }
                }

                // /// Traversing an owner node recursively to the top.
                // fn traverse_owner(tcx: &TyCtxt, owner_node: OwnerNode, mut ctr: usize) {
                //     if ctr > 3 {
                //         // limit recursion. I guess I don't understand this.
                //         return;
                //     }
                //     ctr += 1;
                //     match owner_node {
                //         OwnerNode::Item(item) => {
                //             log::trace!("   owner is an item {:?}", item.ident);
                //             traverse_owner(tcx, tcx.hir().owner(item.owner_id), ctr);
                //         }
                //         OwnerNode::ForeignItem(foreign_item) => {
                //             log::trace!("   owner is a foreign item {:?}", foreign_item.ident);
                //             traverse_owner(tcx, tcx.hir().owner(foreign_item.owner_id), ctr);
                //         }
                //         OwnerNode::TraitItem(trait_item) => {
                //             log::trace!("   owner is an item {:?}", trait_item.ident);
                //             traverse_owner(tcx, tcx.hir().owner(trait_item.owner_id), ctr);
                //         }
                //         OwnerNode::ImplItem(impl_item) => {
                //             log::trace!("   owner is an item {:?}", impl_item.ident);
                //             traverse_owner(tcx, tcx.hir().owner(impl_item.owner_id), ctr);
                //         }
                //         OwnerNode::Crate(mot) => log::trace!("   owner is an item"),
                //     }
                // }

                // Check out the owner of this impl item, i.e. we want to know the trait
                // traverse_owner(self.tcx, self.tcx.hir().owner(ii.owner_id), 0);

                // match &ii.kind {
                //     ImplItemKind::Const(_, _) => (), // log::trace!(" >>> impl const {:#?}", ii.ident),
                //     ImplItemKind::Type(_) => log::trace!(" >>> impl type {:#?}", ii.ident),
                //     ImplItemKind::Fn(bounds, ty) => log::trace!(" >>> impl fn {:#?}", ii.ident),
                // }

                self.foreign_items(ii.owner_id.def_id.to_def_id(), ii.span);

                // keep going
                walk_impl_item(self, ii);
            }
            fn visit_foreign_item_ref(&mut self, ii: &'v ForeignItemRef) {
                log::trace!("visiting foreign item ref {:?} at {:?}", ii.ident, ii.span);
                walk_foreign_item_ref(self, ii)
            }
            fn visit_impl_item_ref(&mut self, ii: &'v ImplItemRef) {
                log::trace!("visiting impl item ref {:?} at {:?}", ii.ident, ii.span);
                walk_impl_item_ref(self, ii)
            }
            fn visit_trait_ref(&mut self, t: &'v TraitRef<'v>) {
                log::trace!(" >>> visiting trait ref");
                walk_trait_ref(self, t)
            }
            fn visit_param_bound(&mut self, bounds: &'v GenericBound<'v>) {
                log::trace!(" >>> visiting param bound");
                walk_param_bound(self, bounds)
            }
            fn visit_poly_trait_ref(&mut self, t: &'v PolyTraitRef<'v>) {
                log::trace!(" >>> visiting poly trait ref {:?}", t.span);
                walk_poly_trait_ref(self, t)
            }
            fn visit_variant_data(&mut self, s: &'v VariantData<'v>) {
                log::trace!(" >>> visiting variant data");
                walk_struct_def(self, s)
            }
            fn visit_field_def(&mut self, s: &'v FieldDef<'v>) {
                log::trace!(" >>> visiting field def {:?} at {:?}", s.ident, s.span);
                walk_field_def(self, s)
            }
            fn visit_enum_def(&mut self, enum_definition: &'v EnumDef<'v>, item_id: HirId) {
                log::trace!(" >>> visiting enum def");
                walk_enum_def(self, enum_definition, item_id)
            }
            fn visit_variant(&mut self, v: &'v Variant<'v>) {
                log::trace!(" >>> visiting variant {:?} at {:?}", v.ident, v.span);
                walk_variant(self, v)
            }
            fn visit_label(&mut self, label: &'v rustc_ast::ast::Label) {
                log::trace!(" >>> visiting label {:?}", label.ident);
                walk_label(self, label)
            }
            fn visit_infer(&mut self, inf: &'v InferArg) {
                log::trace!(" >>> visiting infer {:?}", inf.span);
                walk_inf(self, inf);
            }
            fn visit_generic_arg(&mut self, generic_arg: &'v GenericArg<'v>) {
                log::trace!("visiting generic arg");
                walk_generic_arg(self, generic_arg);
            }
            fn visit_lifetime(&mut self, lifetime: &'v Lifetime) {
                log::trace!(" >>> visiting lifetime {:?}", lifetime.ident);
                walk_lifetime(self, lifetime)
            }
            // The span is that of the surrounding type/pattern/expr/whatever.
            fn visit_qpath(&mut self, qpath: &'v QPath<'v>, id: HirId, span: Span) {
                log::trace!("visiting qpath {span:?}");
                skip_derived!(self, id);

                // Look for foreign paths
                match qpath {
                    QPath::Resolved(ty, path) => match path.res {
                        _ => (),
                    },
                    QPath::TypeRelative(ty, path) => (),
                    QPath::LangItem(item, span, hir_id) => {
                        log::trace!("   language item {:?}", item);
                    }
                }

                walk_qpath(self, qpath, id)
            }
            fn visit_path(&mut self, path: &Path<'v>, id: HirId) {
                log::trace!("visiting path {:?}", path.span);
                skip_derived!(self, id);
                // log::trace!("   node: {:?}", self.tcx.hir().find(id));
                // log::trace!("   path: {:?}", path);

                match path.res {
                    def::Res::Def(def_kind, def_id) => {
                        if !def_id.is_local() {
                            log::trace!("   non local path at: {:?}", path.span);
                            // self.extern_crate(path.span);
                        }
                        match def_kind {
                            def::DefKind::Fn => log::trace!("  path is Fn"),
                            def::DefKind::Trait => log::trace!("  path trait"),
                            _ => log::trace!("  path is def {:?}", def_kind),
                        }
                    }
                    _ => (),
                }

                walk_path(self, path)
            }
            fn visit_path_segment(&mut self, path_segment: &'v PathSegment<'v>) {
                log::trace!("visiting path segment {:?}", path_segment.ident);
                walk_path_segment(self, path_segment)
            }
            fn visit_generic_args(&mut self, generic_args: &'v GenericArgs<'v>) {
                log::trace!("visiting generic args {:?}", generic_args.span_ext);
                walk_generic_args(self, generic_args)
            }
            fn visit_assoc_type_binding(&mut self, type_binding: &'v TypeBinding<'v>) {
                log::trace!(" >>> visiting assoc type binding {:?}", type_binding.span);
                // self.no_assoc_items(type_binding.span);

                // keep going
                walk_assoc_type_binding(self, type_binding);
            }
            fn visit_attribute(&mut self, attr: &'v rustc_ast::ast::Attribute) {
                log::trace!("visiting attribute: {:?}", attr.span);
                // match &attr.kind {
                //     ast::AttrKind::Normal(normal_attr) => {
                //         log::trace!(" >>> normal attribute: {:?}", normal_attr.item.path);
                //     }
                //     ast::AttrKind::DocComment(comment_kind, symbol) => (),
                // }
            }
            fn visit_associated_item_kind(&mut self, kind: &'v AssocItemKind) {
                log::trace!("visit assoc item kind {:?}", kind);
                // self.no_assoc_items(self.span);

                // keep going
                walk_associated_item_kind(self, kind);
            }
            fn visit_defaultness(&mut self, defaultness: &'v Defaultness) {
                log::trace!(" >>> visiting defaultness");
                walk_defaultness(self, defaultness);
            }
            fn visit_inline_asm(&mut self, asm: &'v InlineAsm<'v>, id: HirId) {
                log::trace!(" >>> visiting inline asm");
                self.no_unsafe(asm.line_spans[0]); // XXX: what's the right span here?

                // don't keep going
                // walk_inline_asm(self, asm, id);
            }
        }

        // XXX: read from config file or something
        let derive_allow_list = vec![
            // serde
            "_serde",
            "serde",
            // std lib
            "$crate::marker::StructuralPartialEq",
            "$crate::marker::StructuralEq",
            "$crate::cmp::PartialEq",
            "$crate::cmp::Eq",
            "$crate::clone::Clone",
            "$crate::clone::Clone::clone",
            "$crate::fmt::Debug",
            "$crate::marker::Copy",
            "$crate::hash::Hash",
            "$crate::cmp::PartialOrd",
            "$crate::cmp::Ord",
        ];
        let derive_allow_list = derive_allow_list
            .into_iter()
            .map(|s| s.to_string())
            .collect();
        let trait_block_list = vec!["FnMut"];
        let trait_block_list = trait_block_list
            .into_iter()
            .map(|s| s.to_string())
            .collect();

        let mut linter = HirLinter {
            session,
            tcx: &tcx,
            derive_allow_list,
            trait_block_list,
        };
        hir.visit_all_item_likes_in_crate(&mut linter);
    }

    // let mut bodies = bodies.collect::<Vec<_>>();
    // // we first visit `AnonConst`s, otherwise the thir body might be stolen
    // bodies.sort_by(|a, b| {
    //     use std::cmp::Ordering::*;
    //     let is_anon_const = |x: &rustc_span::def_id::LocalDefId| {
    //         matches!(hir.get_by_def_id(x.clone()), rustc_hir::Node::AnonConst(_))
    //     };
    //     if is_anon_const(a) {
    //         Less
    //     } else if is_anon_const(b) {
    //         Equal
    //     } else {
    //         Greater
    //     }
    // });

    // let thirs: std::collections::HashMap<
    //     rustc_span::def_id::LocalDefId,
    //     (rustc_middle::thir::Thir<'tcx>, ExprId),
    // > = bodies
    //     .into_iter()
    //     .map(|did| {
    //         let (thir, expr) = tcx
    //             .thir_body(rustc_middle::ty::WithOptConstParam {
    //                 did,
    //                 const_param_did: None,
    //             })
    //             .expect("While trying to reach a body's THIR defintion, got a typechecking error");
    //         // Borrowing `Thir` from a `Steal`!
    //         (did, (thir.borrow().clone(), expr))
    //     })
    //     .collect();

    // let items = hir.items();
    // let macro_calls_r = box macro_calls;
    // let state = &thir_export::State {
    //     tcx,
    //     options: box options.clone(),
    //     thir: (),
    //     owner_id: (),
    //     opt_def_id: None,
    //     macro_infos: macro_calls_r,
    //     local_ident_map: Rc::new(RefCell::new(HashMap::new())),
    //     cached_thirs: thirs,
    // };
    // let converted_items = thir_export::inline_macro_invokations(&items.collect(), state);

    // serde_json::to_writer_pretty(options.output_file.open_or_stdout(), &converted_items).unwrap();
}

use std::collections::HashMap;

fn collect_macros(
    crate_ast: &rustc_ast::ast::Crate,
) -> HashMap<rustc_span::Span, rustc_ast::ast::MacCall> {
    use {rustc_ast::ast::*, rustc_ast::visit::*};
    struct MacroCollector {
        macro_calls: HashMap<rustc_span::Span, MacCall>,
    }
    impl<'ast> Visitor<'ast> for MacroCollector {
        fn visit_mac_call(&mut self, mac: &'ast rustc_ast::ast::MacCall) {
            self.macro_calls.insert(mac.span(), mac.clone());
            rustc_ast::visit::walk_mac(self, mac);
        }
    }
    let mut v = MacroCollector {
        macro_calls: HashMap::new(),
    };
    v.visit_crate(crate_ast);
    v.macro_calls
}

use rustc_interface::interface;
use rustc_session::parse::ParseSess;
use rustc_span::symbol::Symbol;

struct DefaultCallbacks {
    options: thir_export::Options,
}

impl Callbacks for DefaultCallbacks {
    fn config(&mut self, config: &mut interface::Config) {
        let options = self.options.clone();
        config.parse_sess_created = Some(Box::new(move |parse_sess| {
            parse_sess.env_depinfo.get_mut().insert((
                Symbol::intern("THIR_EXPORT_OPTIONS"),
                Some(Symbol::intern(&serde_json::to_string(&options).unwrap())),
            ));
        }));
    }

    fn after_parsing<'tcx>(
        &mut self,
        _compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        Compilation::Continue
    }
    fn after_expansion<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        let macro_calls = collect_macros(&queries.parse().unwrap().peek());
        let session = compiler.session();
        queries
            .global_ctxt()
            .unwrap()
            .peek_mut()
            .enter(|tcx| browse_items(&self.options, macro_calls, tcx, session));

        Compilation::Continue
    }
}

fn rustc_sysroot() -> String {
    std::process::Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .ok()
        .and_then(|out| String::from_utf8(out.stdout).ok())
        .map(|s| s.trim().to_string())
        .unwrap()
}

use clap::Parser;
fn main() {
    let _ = pretty_env_logger::try_init();
    let args: Vec<String> = std::env::args().collect();
    let options: thir_export::Options = serde_json::from_str(
        &std::env::var("THIR_EXPORT_OPTIONS")
            .expect("Cannot find environnement variable THIR_EXPORT_OPTIONS"),
    )
    .expect("Invalid value for the environnement variable THIR_EXPORT_OPTIONS");

    let mut rustc_args: Vec<String> = std::env::args().skip(1).collect();
    if !rustc_args.iter().any(|arg| arg.starts_with("--sysroot")) {
        rustc_args.extend(vec!["--sysroot".into(), rustc_sysroot()])
    };

    std::process::exit(rustc_driver::catch_with_exit_code(move || {
        rustc_driver::RunCompiler::new(&rustc_args, &mut DefaultCallbacks { options }).run()
    }))
}

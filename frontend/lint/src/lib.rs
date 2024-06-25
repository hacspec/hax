#![feature(rustc_private)]

// rustc middle
extern crate rustc_middle;
use hax_diagnostics::error;
use rustc_middle::hir::nested_filter::OnlyBodies;
use rustc_middle::ty::TyCtxt;

// rustc errors
extern crate rustc_errors;
use rustc_errors::DiagCtxt;

// rustc hir
extern crate rustc_hir;

use rustc_hir::{intravisit::*, *};

// rustc span
extern crate rustc_span;
use rustc_span::{def_id::LocalDefId, symbol::Ident, Span, Symbol};

// rustc data_structures
extern crate rustc_data_structures;

// rustc ast
extern crate rustc_ast;
use rustc_ast::ast;

#[derive(Debug, Clone, Copy)]
pub enum Type {
    Rust,
    Hacspec,
}

pub struct Linter<'tcx> {
    tcx: TyCtxt<'tcx>,
    extern_allow_list: Vec<&'static str>,
    trait_block_list: Vec<String>,
    ltype: Type,
}

impl<'tcx> Linter<'tcx> {
    /// Register the linter.
    pub fn register(tcx: TyCtxt<'tcx>, ltype: Type) {
        let hir = tcx.hir();

        let trait_block_list = vec!["FnMut"];
        let trait_block_list = trait_block_list
            .into_iter()
            .map(|s| s.to_string())
            .collect();

        let mut extern_allow_list = vec!["core", "alloc", "std"];
        if matches!(ltype, Type::Hacspec) {
            extern_allow_list.append(&mut vec![
                "hacspec_lib",
                "secret_integers",
                "abstract_integers",
            ]);
        }

        let mut linter = Self {
            tcx,
            extern_allow_list,
            trait_block_list,
            ltype,
        };
        hir.visit_all_item_likes_in_crate(&mut linter);
    }

    fn dcx(&self) -> &'tcx DiagCtxt {
        self.tcx.dcx()
    }
}

fn has_attr(attrs: &[ast::Attribute], symbol: Symbol) -> bool {
    attrs.iter().any(|attr| attr.has_name(symbol))
}

macro_rules! skip_derived_non_local {
    ($self:ident, $hir_id:expr) => {
        if $self.any_parent_is_automatically_derived($hir_id) {
            tracing::trace!("   skipping automatically derived code");
            return;
        }
        if $self.non_local_hir_id($hir_id) {
            error::extern_crate($self.dcx(), $self.tcx.def_span($hir_id.owner));
            // Don't keep going
            return;
        }
    };
}

macro_rules! skip_v1_lib_macros {
    ($self:ident, $hir_id:expr) => {
        if $self
            .tcx
            .def_span($hir_id.owner)
            .macro_backtrace()
            .any(|data| {
                if let Some(parent) = data.parent_module {
                    tracing::trace!("  macro in {:?}", { data.parent_module });
                    if $self.non_local_def_id(parent, $self.tcx.def_span($hir_id.owner)) {
                        return true;
                    }
                }
                false
            })
        {
            return;
        }
    };
}

impl<'v> Linter<'v> {
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

    /// Check and warn for non-local def ids.
    ///
    /// Returns true if the path is non-local.
    fn non_local_def_id(&self, def_id: rustc_span::def_id::DefId, span: Span) -> bool {
        if !def_id.is_local() {
            tracing::trace!("   non local path at: {:?}", span);

            let krate = self.tcx.crate_name(def_id.krate);
            tracing::trace!("   crate: {:?}", krate);
            if self.extern_allow_list.contains(&krate.as_str()) {
                // For the allow list we assume that there's a model
                return true;
            }
            // On everything else we warn.
            error::extern_crate(self.dcx(), span);
            // }
            return true;
        }
        false
    }

    /// Check and warn for non-local paths.
    ///
    /// Returns true if the path is non-local.
    fn non_local_path(&self, qpath: &QPath) -> bool {
        match qpath {
            QPath::Resolved(_, path) => match path.res {
                def::Res::Def(_def_kind, def_id) => self.non_local_def_id(def_id, path.span),
                _ => return false,
            },
            _ => return false,
        }
    }

    /// Check and warn for non-local hir ids.
    ///
    /// Returns true if the path is non-local.
    fn non_local_hir_id(&self, hir_id: HirId) -> bool {
        if self.non_local_def_id(hir_id.owner.to_def_id(), self.tcx.def_span(hir_id.owner)) {
            return true;
        }
        false
    }
}

impl<'v> Visitor<'v> for Linter<'v> {
    type NestedFilter = OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        tracing::trace!("visiting nested map");
        self.tcx.hir()
    }

    fn visit_nested_trait_item(&mut self, id: TraitItemId) {
        tracing::trace!("visiting nested trait item");

        walk_trait_item(self, self.tcx.hir().trait_item(id));
    }
    fn visit_nested_impl_item(&mut self, id: ImplItemId) {
        tracing::trace!("visiting nested impl item");

        walk_impl_item(self, self.tcx.hir().impl_item(id));
    }
    fn visit_nested_foreign_item(&mut self, _id: ForeignItemId) {
        tracing::trace!("visiting nested foreign item");
    }
    fn visit_nested_body(&mut self, id: BodyId) {
        tracing::trace!("visiting nested body");

        walk_body(self, self.tcx.hir().body(id));
    }

    fn visit_item(&mut self, i: &'v Item<'v>) {
        tracing::trace!("visiting item {:?} at {:?}", i.ident.name, i.span);
        skip_derived_non_local!(self, i.hir_id());
        skip_v1_lib_macros!(self, i.hir_id());
        // tracing::trace!("   item kind: {:#?}", i.kind);

        match i.kind {
            ItemKind::Union(_, _) => {
                // TODO: This should be an error (span_err_with_code)
                error::no_union(self.dcx(), i.span);
                // self.no_union(i.span)
            }
            ItemKind::GlobalAsm(_) => error::no_unsafe(self.dcx(), i.span),
            ItemKind::Impl(imp) => {
                // tracing::trace!("     impl {:?}", imp.self_ty.kind);
                if imp.safety == Safety::Unsafe {
                    error::no_unsafe(self.dcx(), i.span);
                }
                if let Some(of_trait) = &imp.of_trait {
                    let def_id = of_trait.hir_ref_id.owner.def_id.to_def_id();
                    if self
                        .tcx
                        .has_attr(def_id, rustc_span::symbol::sym::automatically_derived)
                    {
                        tracing::trace!("   Skipping automatically derived implementations");
                        return;
                    }
                }
            }
            _ => (),
        }

        // Check for foreign item
        if self.non_local_def_id(i.owner_id.def_id.to_def_id(), i.span) {
            // Don't keep walking.
            return;
        }

        // keep going
        walk_item(self, i);
    }
    fn visit_body(&mut self, b: &Body<'v>) {
        tracing::trace!("visiting body");
        skip_derived_non_local!(self, b.value.hir_id);

        // keep going
        walk_body(self, b);
    }

    ///////////////

    fn visit_id(&mut self, hir_id: HirId) {
        tracing::trace!(
            "visiting id {hir_id:?} from def path {:?}",
            self.tcx.def_path(hir_id.owner.to_def_id())
        );

        skip_derived_non_local!(self, hir_id);
        skip_v1_lib_macros!(self, hir_id);

        // Nothing to do.
    }
    fn visit_name(&mut self, name: Symbol) {
        tracing::trace!("visiting name {:?}", name);
        // Nothing to do.
    }
    fn visit_ident(&mut self, ident: Ident) {
        tracing::trace!("visiting ident {:?}", ident);

        // XXX: This really shouldn't be done here but earlier.
        if ident.name.as_str() == "FnMut" {
            error::no_fn_mut(self.dcx(), ident.span);
            return;
        }

        walk_ident(self, ident)
    }
    fn visit_mod(&mut self, m: &'v Mod<'v>, s: Span, n: HirId) {
        tracing::trace!("visiting mod {:?}", s);

        // keep going
        walk_mod(self, m, n);
    }
    fn visit_foreign_item(&mut self, i: &'v ForeignItem<'v>) {
        tracing::trace!("visiting foreign item {:?} at {:?}", i.ident, i.span);
        walk_foreign_item(self, i)
    }
    fn visit_local(&mut self, l: &'v LetStmt<'v>) {
        tracing::trace!("visiting local {:?}", l.span);
        walk_local(self, l)
    }
    fn visit_block(&mut self, b: &'v Block<'v>) {
        tracing::trace!("visiting block {:?}", b.span);

        skip_derived_non_local!(self, b.hir_id);

        walk_block(self, b)
    }
    fn visit_stmt(&mut self, s: &'v Stmt<'v>) {
        tracing::trace!(
            "visiting stmt {:?} at {:?}",
            self.tcx.opt_item_name(s.hir_id.owner.to_def_id()).unwrap(),
            s.span
        );
        skip_derived_non_local!(self, s.hir_id);

        match &s.kind {
            StmtKind::Let(b) => {
                // tracing::trace!("       local stmt");
                if let Some(init) = b.init {
                    match init.kind {
                        ExprKind::AddrOf(x, f, _s) => {
                            // Don't allow raw borrows (pointer) and mutable borrows.
                            if matches!(x, BorrowKind::Raw) || matches!(f, Mutability::Mut) {
                                error::mut_borrow_let(self.dcx(), b.span)
                            }
                        }
                        _ => (),
                    }
                }
                if let Some(_els) = b.els {}
            }
            StmtKind::Item(_) => (), // tracing::trace!("       item stmt"),
            StmtKind::Expr(_) => (), // tracing::trace!("       expr stmt"),
            StmtKind::Semi(_) => (), // tracing::trace!("       semi stmt"),
        }

        // keep going
        walk_stmt(self, s);
    }
    fn visit_arm(&mut self, a: &'v Arm<'v>) {
        tracing::trace!("visiting arm {:?}", a.span);
        walk_arm(self, a)
    }
    fn visit_pat(&mut self, p: &'v Pat<'v>) {
        tracing::trace!("visiting pat {:?}", p.span);
        walk_pat(self, p)
    }
    fn visit_pat_field(&mut self, f: &'v PatField<'v>) {
        tracing::trace!("visiting pat field {:?} at {:?}", f.ident, f.span);
        walk_pat_field(self, f)
    }
    fn visit_array_length(&mut self, len: &'v ArrayLen) {
        tracing::trace!("visiting array length");
        walk_array_len(self, len)
    }
    fn visit_anon_const(&mut self, c: &'v AnonConst) {
        tracing::trace!("visiting anon const");
        walk_anon_const(self, c)
    }
    fn visit_expr(&mut self, ex: &'v Expr<'v>) {
        tracing::trace!("visiting expr {:?}", ex.span);
        skip_derived_non_local!(self, ex.hir_id);
        // tracing::trace!("   Node: {:#?}", self.tcx.hir().find(ex.hir_id));

        // eprintln!("  kind: {:?}", ex.kind);
        // eprintln!("expr at: {:?}", self.expr_span(ex));

        match &ex.kind {
            ExprKind::Block(block, _) => match block.rules {
                BlockCheckMode::UnsafeBlock(UnsafeSource::UserProvided) => {
                    error::no_unsafe(self.dcx(), block.span)
                }
                _ => (),
            },
            ExprKind::Loop(_block, _label, source, span) => match source {
                LoopSource::Loop | LoopSource::While => error::unsupported_loop(self.dcx(), *span),
                LoopSource::ForLoop => tracing::trace!("hir for loop"),
            },
            // FIXME: where to get this from?
            // ExprKind::Async(e, c, b) => self.no_async_await(b.span),
            // ExprKind::Await(a) => self.no_async_await(a.span),
            ExprKind::InlineAsm(p) => error::no_unsafe(self.dcx(), p.line_spans[0]),
            ExprKind::Call(expr, _exprs) => {
                // tracing::trace!("call: {:#?}", expr);
                if self.tcx.is_foreign_item(expr.hir_id.owner.def_id) {
                    tracing::trace!("foreign call: {:#?}", expr.span);
                }
            }
            ExprKind::MethodCall(_path, expr, _exprs, _span) => {
                // tracing::trace!("method call: {:#?}", path);
                if self.tcx.is_foreign_item(expr.hir_id.owner.def_id) {
                    tracing::trace!("foreign method call: {:#?}", expr.span);
                }
            }
            ExprKind::Path(qpath) => {
                if self.non_local_path(qpath) {
                    // Don't keep walking.
                    return;
                }
            }
            _ => (),
        }

        // keep going
        walk_expr(self, ex);
    }
    fn visit_expr_field(&mut self, field: &'v ExprField<'v>) {
        tracing::trace!("visiting expr field {:?}", field.ident);
        walk_expr_field(self, field)
    }
    fn visit_ty(&mut self, t: &'v Ty<'v>) {
        tracing::trace!("visiting ty {:?}", t.span);
        walk_ty(self, t)
    }
    fn visit_generic_param(&mut self, p: &'v GenericParam<'v>) {
        tracing::trace!("visiting generic param {:?}", p.span);
        tracing::trace!("   name: {:?}", p.name);

        walk_generic_param(self, p)
    }
    fn visit_const_param_default(&mut self, _param: HirId, ct: &'v AnonConst) {
        tracing::trace!("visiting const param default");
        walk_const_param_default(self, ct)
    }
    fn visit_generics(&mut self, g: &'v Generics<'v>) {
        tracing::trace!("visiting generics {:?}", g.span);
        walk_generics(self, g)
    }
    fn visit_where_predicate(&mut self, predicate: &'v WherePredicate<'v>) {
        tracing::trace!("visiting where predicate");

        match predicate {
            WherePredicate::BoundPredicate(p) => {
                // tracing::trace!("   bound predicate {:#?}", p.bounds);
                for bound in p.bounds {
                    match bound {
                        GenericBound::Trait(trait_ref, _bound_modifier) => {
                            tracing::trace!("  trait bound {:?}", trait_ref);
                            // tracing::trace!(
                            //     "  node {:#?}",
                            //     self.tcx.hir().get(trait_ref.trait_ref.hir_ref_id)
                            // );
                        }
                        _ => (),
                    }
                }
            }
            WherePredicate::RegionPredicate(p) => error::explicit_lifetime(self.dcx(), p.span),
            WherePredicate::EqPredicate(p) => {
                tracing::trace!("   eq predicate {:?}/{:?}", p.lhs_ty, p.rhs_ty);
            }
        }

        // keep going
        walk_where_predicate(self, predicate);
    }
    fn visit_fn_ret_ty(&mut self, ret_ty: &'v FnRetTy<'v>) {
        tracing::trace!("visiting fn ret ty");
        walk_fn_ret_ty(self, ret_ty)
    }
    fn visit_fn_decl(&mut self, fd: &'v FnDecl<'v>) {
        tracing::trace!("visiting fn decl");
        walk_fn_decl(self, fd)
    }
    fn visit_fn(
        &mut self,
        fk: FnKind<'v>,
        fd: &'v FnDecl<'v>,
        b: BodyId,
        span: Span,
        id: LocalDefId,
    ) {
        tracing::trace!("visiting fn at {:?}", span);

        let hir_id = self.tcx.local_def_id_to_hir_id(id);

        skip_derived_non_local!(self, hir_id);
        skip_v1_lib_macros!(self, hir_id);

        fn check_ty_kind(visitor: &Linter, k: &TyKind, span: Span) {
            match k {
                TyKind::Ptr(_) => error::no_unsafe(visitor.dcx(), span),
                TyKind::TraitObject(_, _, _) => {
                    error::no_trait_objects(visitor.dcx(), span);
                }
                TyKind::Ref(lifetime, ty) => {
                    // TODO: check lifetime. only allow anonymous
                    tracing::trace!("   lifetime {:?}", lifetime.ident);
                    // tracing::trace!("   ref ty {:#?}", ty);

                    // check for mutable self.
                    // we have to do that here, because we know it's mut here.
                    if matches!(ty.mutbl, Mutability::Mut) {
                        if matches!(visitor.ltype, Type::Hacspec) {
                            // No mutability is allowed here for hacspec
                            error::no_mut(visitor.dcx(), ty.ty.span);
                            return;
                        }
                        match &ty.ty.kind {
                            TyKind::Path(path) => match path {
                                QPath::Resolved(_ty, p) => {
                                    if p.segments[0].ident.as_str() == "Self" {
                                        error::no_mut_self(visitor.dcx(), p.span)
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
                    error::no_trait_objects(visitor.dcx(), span);
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
                            error::no_trait_objects(visitor.dcx(), span);
                        }
                    }
                    QPath::TypeRelative(ty, _p) => check_ty_kind(visitor, &ty.kind, span),
                    QPath::LangItem(_lang_item, _span) => (),
                },
                _ => (),
            }
        }

        match fk {
            FnKind::ItemFn(ident, generics, header) => {
                tracing::trace!("   ItemFn: {:?}", ident);
                // TODO: All this should be an error (span_err_with_code)
                // Unsafe functions
                if header.safety == Safety::Unsafe {
                    error::no_unsafe(self.dcx(), span);
                }

                // async functions
                if let IsAsync::Async(_) = header.asyncness {
                    error::no_async_await(self.dcx(), span);
                }

                // Check generics for lifetimes
                for predicate in generics.predicates {
                    match &predicate {
                        WherePredicate::RegionPredicate(region) => {
                            error::explicit_lifetime(self.dcx(), region.span)
                        }
                        WherePredicate::BoundPredicate(bound) => {
                            for bound in bound.bounds {
                                match bound {
                                    GenericBound::Trait(poly_ref, _modifier) => {
                                        let path_string = poly_ref
                                            .trait_ref
                                            .path
                                            .segments
                                            .iter()
                                            .map(|seg| seg.ident.as_str())
                                            .collect::<Vec<&str>>()
                                            .join("::");
                                        tracing::trace!(
                                            "   trait implementation of {:?}",
                                            path_string
                                        );

                                        if self.trait_block_list.contains(&path_string) {
                                            error::unsupported_item(
                                                self.dcx(),
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
                                error::explicit_lifetime(self.dcx(), param.span)
                            }
                            _ => (),
                        },
                        _ => (),
                    }
                }
            }
            FnKind::Method(ident, sig) => {
                tracing::trace!("   Method: {:?}", ident);
                // TODO: All this should be an error (span_err_with_code)
                // Unsafe functions
                if sig.header.safety == Safety::Unsafe {
                    error::no_unsafe(self.dcx(), span);
                }

                // async functions
                if let IsAsync::Async(_) = sig.header.asyncness {
                    error::no_async_await(self.dcx(), span);
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
            // tracing::trace!("fd inputs {:#?}", param);
            check_ty_kind(self, &param.kind, param.span);
        });

        // keep going
        walk_fn(self, fk, fd, b, id);
    }
    fn visit_use(&mut self, path: &'v UsePath<'v>, hir_id: HirId) {
        // FIXME
        tracing::trace!("visiting use {:?}", path.span);

        // keep going
        walk_use(self, path, hir_id);
    }
    fn visit_trait_item(&mut self, ti: &'v TraitItem<'v>) {
        tracing::trace!("visiting trait item {:?} at {:?}", ti.ident.name, ti.span);
        skip_derived_non_local!(self, ti.hir_id());

        // match &ti.kind {
        //     TraitItemKind::Const(_, _) => self.no_assoc_items(ti.span),
        //     TraitItemKind::Type(_, _) => self.no_assoc_items(ti.span),
        //     TraitItemKind::Fn(bounds, ty) => (),
        // }

        // keep going
        walk_trait_item(self, ti);
    }
    fn visit_trait_item_ref(&mut self, ii: &'v TraitItemRef) {
        tracing::trace!("visiting trait item ref {:?} at {:?}", ii.ident, ii.span);
        walk_trait_item_ref(self, ii)
    }
    fn visit_impl_item(&mut self, ii: &'v ImplItem<'v>) {
        tracing::trace!("visiting impl item {:?} at {:?}", ii.ident.name, ii.span,);
        skip_derived_non_local!(self, ii.hir_id());

        // tracing::trace!("   item: {:#?}", ii);

        // Check the trait for this item.
        for predicate in ii.generics.predicates {
            match predicate {
                WherePredicate::BoundPredicate(bound) => {
                    for bound in bound.bounds {
                        match bound {
                            GenericBound::Trait(_poly_ref, _modifier) => {
                                tracing::trace!("   Skipping trait bound");
                                return;
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
        //             tracing::trace!("   owner is an item {:?}", item.ident);
        //             traverse_owner(tcx, tcx.hir().owner(item.owner_id), ctr);
        //         }
        //         OwnerNode::ForeignItem(foreign_item) => {
        //             tracing::trace!("   owner is a foreign item {:?}", foreign_item.ident);
        //             traverse_owner(tcx, tcx.hir().owner(foreign_item.owner_id), ctr);
        //         }
        //         OwnerNode::TraitItem(trait_item) => {
        //             tracing::trace!("   owner is an item {:?}", trait_item.ident);
        //             traverse_owner(tcx, tcx.hir().owner(trait_item.owner_id), ctr);
        //         }
        //         OwnerNode::ImplItem(impl_item) => {
        //             tracing::trace!("   owner is an item {:?}", impl_item.ident);
        //             traverse_owner(tcx, tcx.hir().owner(impl_item.owner_id), ctr);
        //         }
        //         OwnerNode::Crate(mot) => tracing::trace!("   owner is an item"),
        //     }
        // }

        // Check out the owner of this impl item, i.e. we want to know the trait
        // traverse_owner(self.tcx, self.tcx.hir().owner(ii.owner_id), 0);

        // match &ii.kind {
        //     ImplItemKind::Const(_, _) => (), // tracing::trace!("impl const {:#?}", ii.ident),
        //     ImplItemKind::Type(_) => tracing::trace!("impl type {:#?}", ii.ident),
        //     ImplItemKind::Fn(bounds, ty) => tracing::trace!("impl fn {:#?}", ii.ident),
        // }

        if self.non_local_def_id(ii.owner_id.def_id.to_def_id(), ii.span) {
            // Don't keep walking.
            return;
        }

        // keep going
        walk_impl_item(self, ii);
    }
    fn visit_foreign_item_ref(&mut self, ii: &'v ForeignItemRef) {
        tracing::trace!("visiting foreign item ref {:?} at {:?}", ii.ident, ii.span);
        walk_foreign_item_ref(self, ii)
    }
    fn visit_impl_item_ref(&mut self, ii: &'v ImplItemRef) {
        tracing::trace!("visiting impl item ref {:?} at {:?}", ii.ident, ii.span);
        walk_impl_item_ref(self, ii)
    }
    fn visit_trait_ref(&mut self, t: &'v TraitRef<'v>) {
        tracing::trace!("visiting trait ref");
        walk_trait_ref(self, t)
    }
    fn visit_param_bound(&mut self, bounds: &'v GenericBound<'v>) {
        tracing::trace!("visiting param bound");
        walk_param_bound(self, bounds)
    }
    fn visit_poly_trait_ref(&mut self, t: &'v PolyTraitRef<'v>) {
        tracing::trace!("visiting poly trait ref {:?}", t.span);
        walk_poly_trait_ref(self, t)
    }
    fn visit_variant_data(&mut self, s: &'v VariantData<'v>) {
        tracing::trace!("visiting variant data");
        walk_struct_def(self, s)
    }
    fn visit_field_def(&mut self, s: &'v FieldDef<'v>) {
        tracing::trace!("visiting field def {:?} at {:?}", s.ident, s.span);
        walk_field_def(self, s)
    }
    fn visit_enum_def(&mut self, enum_definition: &'v EnumDef<'v>, item_id: HirId) {
        tracing::trace!("visiting enum def");
        walk_enum_def(self, enum_definition, item_id)
    }
    fn visit_variant(&mut self, v: &'v Variant<'v>) {
        tracing::trace!("visiting variant {:?} at {:?}", v.ident, v.span);
        walk_variant(self, v)
    }
    fn visit_label(&mut self, label: &'v rustc_ast::ast::Label) {
        tracing::trace!("visiting label {:?}", label.ident);
        walk_label(self, label)
    }
    fn visit_infer(&mut self, inf: &'v InferArg) {
        tracing::trace!("visiting infer {:?}", inf.span);
        walk_inf(self, inf);
    }
    fn visit_generic_arg(&mut self, generic_arg: &'v GenericArg<'v>) {
        tracing::trace!("visiting generic arg");
        walk_generic_arg(self, generic_arg);
    }
    fn visit_lifetime(&mut self, lifetime: &'v Lifetime) {
        tracing::trace!("visiting lifetime {:?}", lifetime.ident);
        walk_lifetime(self, lifetime)
    }
    // The span is that of the surrounding type/pattern/expr/whatever.
    fn visit_qpath(&mut self, qpath: &'v QPath<'v>, id: HirId, span: Span) {
        tracing::trace!("visiting qpath {span:?}");
        skip_derived_non_local!(self, id);

        // Look for foreign paths
        match qpath {
            QPath::Resolved(_ty, path) => match path.res {
                _ => (),
            },
            QPath::TypeRelative(_ty, _path) => (),
            QPath::LangItem(item, _span) => {
                tracing::trace!("   language item {:?}", item);
            }
        }

        walk_qpath(self, qpath, id)
    }
    fn visit_path(&mut self, path: &Path<'v>, id: HirId) {
        tracing::trace!("visiting path {:?}", path.span);

        skip_derived_non_local!(self, id);
        skip_v1_lib_macros!(self, id);
        // tracing::trace!("   node: {:?}", self.tcx.hir().find(id));
        // tracing::trace!("   path: {:?}", path);

        match path.res {
            def::Res::Def(def_kind, def_id) => {
                if !def_id.is_local() {
                    tracing::trace!("   non local path at: {:?}", path.span);
                    // self.extern_crate(path.span);
                }
                match def_kind {
                    def::DefKind::Fn => tracing::trace!("  path is Fn"),
                    def::DefKind::Trait => tracing::trace!("  path trait"),
                    _ => tracing::trace!("  path is def {:?}", def_kind),
                }
            }
            _ => (),
        }

        walk_path(self, path)
    }
    fn visit_path_segment(&mut self, path_segment: &'v PathSegment<'v>) {
        tracing::trace!("visiting path segment {:?}", path_segment.ident);
        skip_derived_non_local!(self, path_segment.hir_id);
        walk_path_segment(self, path_segment)
    }
    fn visit_generic_args(&mut self, generic_args: &'v GenericArgs<'v>) {
        tracing::trace!("visiting generic args {:?}", generic_args.span_ext);
        walk_generic_args(self, generic_args)
    }
    fn visit_assoc_item_constraint(&mut self, constraint: &'v AssocItemConstraint<'v>) {
        tracing::trace!("visiting assoc item constraint {:?}", constraint.span);
        // self.no_assoc_items(type_binding.span);

        // keep going
        walk_assoc_item_constraint(self, constraint);
    }
    fn visit_attribute(&mut self, attr: &'v rustc_ast::ast::Attribute) {
        tracing::trace!("visiting attribute: {:?}", attr.span);
        // match &attr.kind {
        //     ast::AttrKind::Normal(normal_attr) => {
        //         tracing::trace!("normal attribute: {:?}", normal_attr.item.path);
        //     }
        //     ast::AttrKind::DocComment(comment_kind, symbol) => (),
        // }
    }
    fn visit_associated_item_kind(&mut self, kind: &'v AssocItemKind) {
        tracing::trace!("visit assoc item kind {:?}", kind);
        // self.no_assoc_items(self.span);

        // keep going
        walk_associated_item_kind(self, kind);
    }
    fn visit_defaultness(&mut self, defaultness: &'v Defaultness) {
        tracing::trace!("visiting defaultness");
        walk_defaultness(self, defaultness);
    }
    fn visit_inline_asm(&mut self, asm: &'v InlineAsm<'v>, _id: HirId) {
        tracing::trace!("visiting inline asm");
        error::no_unsafe(self.dcx(), asm.line_spans[0]); // XXX: what's the right span here?

        // don't keep going
        // walk_inline_asm(self, asm, id);
    }
}

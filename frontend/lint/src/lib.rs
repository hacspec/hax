#![feature(rustc_private)]

// rustc middle
extern crate rustc_middle;
use circus_diagnostics::error;
use rustc_middle::hir::nested_filter::OnlyBodies;
use rustc_middle::ty::TyCtxt;

// rustc hier
extern crate rustc_hir;
use rustc_hir::{intravisit::*, *};

// rustc span
extern crate rustc_span;
use rustc_span::{symbol::Ident, Span, Symbol};

// rustc session
extern crate rustc_session;
use rustc_session::Session;

// rustc data_structures
extern crate rustc_data_structures;
use rustc_data_structures::sync::Lrc;

// rustc ast
extern crate rustc_ast;
use rustc_ast::ast;

pub enum Error {}

pub struct Linter<'a, 'tcx> {
    session: &'a Lrc<Session>,
    tcx: TyCtxt<'tcx>,
    derive_allow_list: Vec<String>,
    trait_block_list: Vec<String>,
}

impl<'a, 'tcx> Linter<'a, 'tcx> {
    /// Register the linter.
    pub fn register(tcx: TyCtxt<'tcx>, session: &'a Lrc<Session>) -> Result<Self, Error> {
        let hir = tcx.hir();

        // XXX: read from config file or something and find a better way to do this.
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

        let mut linter = Self {
            session,
            tcx,
            derive_allow_list,
            trait_block_list,
        };
        hir.visit_all_item_likes_in_crate(&mut linter);
        todo!()
    }
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

impl<'a, 'v> Linter<'a, 'v> {
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

    // XXX: remove
    fn foreign_items(&self, key: rustc_span::def_id::DefId, span: Span) {
        // Check for foreign item
        if self.tcx.is_foreign_item(key) {
            log::trace!("foreign item: {:#?}", span);
        }
    }
}

impl<'v, 'a> Visitor<'v> for Linter<'a, 'v> {
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
    fn visit_nested_foreign_item(&mut self, _id: ForeignItemId) {
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
                error::no_union(self.session, i.span);
                // self.no_union(i.span)
            }
            ItemKind::GlobalAsm(_) => error::no_unsafe(self.session, i.span),
            ItemKind::Impl(imp) => {
                // log::trace!("     impl {:?}", imp.self_ty.kind);
                if imp.unsafety == Unsafety::Unsafe {
                    error::no_unsafe(self.session, imp.items[0].span); // TODO: What's the right span?
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
                                Some((_left, right)) => right[1..].to_string(),
                                None => path_string,
                            };
                            error::derive_external_trait(self.session, i.span, path_string);

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
            error::no_fn_mut(self.session, ident.span);
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
                        ExprKind::AddrOf(x, f, _s) => {
                            // Don't allow raw borrows (pointer) and mutable borrows.
                            if matches!(x, BorrowKind::Raw) || matches!(f, Mutability::Mut) {
                                error::mut_borrow_let(self.session, b.span)
                            }
                        }
                        _ => (),
                    }
                }
                if let Some(_els) = b.els {}
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
                    error::no_unsafe(self.session, block.span)
                }
                _ => (),
            },
            ExprKind::Loop(_block, _label, source, span) => match source {
                LoopSource::Loop | LoopSource::While => {
                    error::unsupported_loop(self.session, *span)
                }
                LoopSource::ForLoop => log::trace!(" >>> hir for loop"),
            },
            // FIXME: where to get this from?
            // ExprKind::Async(e, c, b) => self.no_async_await(b.span),
            // ExprKind::Await(a) => self.no_async_await(a.span),
            ExprKind::InlineAsm(p) => error::no_unsafe(self.session, p.line_spans[0]),
            ExprKind::Call(expr, _exprs) => {
                // log::trace!("call: {:#?}", expr);
                if self.tcx.is_foreign_item(expr.hir_id.owner.def_id) {
                    log::trace!("foreign call: {:#?}", expr.span);
                }
            }
            ExprKind::MethodCall(_path, expr, _exprs, _span) => {
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
                                    log::trace!("   We skip trait implementation of allowlist?");
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
                        GenericBound::LangItemTrait(lang_item, span, _hir_id, _generic_args) => {
                            // XXX: for some reason FnMut is not a lang item
                            log::trace!("  lang trait bound {:?}", span);
                            if matches!(lang_item, LangItem::FnMut) {
                                error::no_fn_mut(self.session, *span);
                            }
                        }
                        GenericBound::Trait(trait_ref, _bound_modifier) => {
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
            WherePredicate::RegionPredicate(p) => error::explicit_lifetime(self.session, p.span),
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
    fn visit_fn(&mut self, fk: FnKind<'v>, fd: &'v FnDecl<'v>, b: BodyId, span: Span, id: HirId) {
        log::trace!(" >>> visiting fn at {:?}", span);
        skip_derived!(self, id);

        fn check_ty_kind(visitor: &Linter, k: &TyKind, span: Span) {
            match k {
                TyKind::Ptr(_) => error::no_unsafe(visitor.session, span),
                TyKind::TraitObject(_, _, _) => {
                    error::no_trait_objects(visitor.session, span);
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
                                QPath::Resolved(_ty, p) => {
                                    if p.segments[0].ident.as_str() == "Self" {
                                        error::no_mut_self(visitor.session, p.span)
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
                    error::no_trait_objects(visitor.session, span);
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
                            error::no_trait_objects(visitor.session, span);
                        }
                    }
                    QPath::TypeRelative(ty, _p) => check_ty_kind(visitor, &ty.kind, span),
                    QPath::LangItem(_lang_item, _span, _hir_id) => (),
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
                    error::no_unsafe(self.session, span);
                }

                // async functions
                if header.asyncness == IsAsync::Async {
                    error::no_async_await(self.session, span);
                }

                // Check generics for lifetimes
                for predicate in generics.predicates {
                    match &predicate {
                        WherePredicate::RegionPredicate(region) => {
                            error::explicit_lifetime(self.session, region.span)
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
                                        log::trace!("   trait implementation of {:?}", path_string);

                                        if self.trait_block_list.contains(&path_string) {
                                            error::unsupported_item(
                                                self.session,
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
                                error::explicit_lifetime(self.session, param.span)
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
                    error::no_unsafe(self.session, span);
                }

                // async functions
                if sig.header.asyncness == IsAsync::Async {
                    error::no_async_await(self.session, span);
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
                            GenericBound::Trait(poly_ref, _modifier) => {
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
                                    log::trace!("    found trait impl for trait {:?}", path_string);
                                    log::trace!("   Skipping trait implementation of allowlist");
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
            QPath::Resolved(_ty, path) => match path.res {
                _ => (),
            },
            QPath::TypeRelative(_ty, _path) => (),
            QPath::LangItem(item, _span, _hir_id) => {
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
    fn visit_inline_asm(&mut self, asm: &'v InlineAsm<'v>, _id: HirId) {
        log::trace!(" >>> visiting inline asm");
        error::no_unsafe(self.session, asm.line_spans[0]); // XXX: what's the right span here?

        // don't keep going
        // walk_inline_asm(self, asm, id);
    }
}

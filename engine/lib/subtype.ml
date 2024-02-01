open! Prelude

module Make
    (FA : Features.T)
    (FB : Features.T)
    (S : Features.SUBTYPE.T with module A = FA and module B = FB) =
struct
  open Ast
  module A = Ast.Make (FA)
  module B = Ast.Make (FB)
  module UA = Ast_utils.Make (FA)
  module UB = Ast_utils.Make (FB)
  module FA = FA

  let dmutability (span : Span.t) (type a b) (s : Span.t -> a -> b)
      (mutability : a mutability) : b mutability =
    match mutability with
    | Mutable w -> Mutable (s span w)
    | Immutable -> Immutable

  let rec dty (span : span) (ty : A.ty) : B.ty =
    match ty with
    | TBool -> TBool
    | TChar -> TChar
    | TInt k -> TInt k
    | TFloat k -> TFloat k
    | TStr -> TStr
    | TApp { ident; args } ->
        TApp { ident; args = List.map ~f:(dgeneric_value span) args }
    | TArray { typ; length } ->
        TArray { typ = dty span typ; length = dexpr length }
    | TSlice { witness; ty } ->
        TSlice { witness = S.slice span witness; ty = dty span ty }
    | TRef { witness; typ; mut; region } ->
        TRef
          {
            witness = S.reference span witness;
            typ = dty span typ;
            mut = dmutability span S.mutable_reference mut;
            region;
          }
    | TParam local_ident -> TParam local_ident
    | TArrow (inputs, output) ->
        TArrow (List.map ~f:(dty span) inputs, dty span output)
    | TAssociatedType { impl; item } ->
        TAssociatedType { impl = dimpl_expr span impl; item }
    | TOpaque ident -> TOpaque ident
    | TRawPointer { witness } ->
        TRawPointer { witness = S.raw_pointer span witness }

  and dtrait_ref (span : span) (r : A.trait_ref) : B.trait_ref =
    { trait = r.trait; args = List.map ~f:(dgeneric_value span) r.args }

  and dimpl_expr (span : span) (i : A.impl_expr) : B.impl_expr =
    match i with
    | Self -> Self
    | Concrete tr -> Concrete (dtrait_ref span tr)
    | LocalBound { id } -> LocalBound { id }
    | Parent { impl; trait } ->
        Parent { impl = dimpl_expr span impl; trait = dtrait_ref span trait }
    | Projection { impl; item; trait } ->
        Projection
          { impl = dimpl_expr span impl; item; trait = dtrait_ref span trait }
    | ImplApp { impl; args } ->
        ImplApp
          {
            impl = dimpl_expr span impl;
            args = List.map ~f:(dimpl_expr span) args;
          }
    | Dyn tr -> Dyn (dtrait_ref span tr)
    | Builtin tr -> Builtin (dtrait_ref span tr)
    | ClosureIE todo -> ClosureIE todo
    | FnPointer ty -> FnPointer (dty span ty)

  and dgeneric_value (span : span) (generic_value : A.generic_value) :
      B.generic_value =
    match generic_value with
    | GLifetime { lt; witness } ->
        GLifetime { lt; witness = S.lifetime span witness }
    | GType t -> GType (dty span t)
    | GConst e -> GConst (dexpr e)

  and dborrow_kind (span : span) (borrow_kind : A.borrow_kind) : B.borrow_kind =
    match borrow_kind with
    | Shared -> Shared
    | Unique -> Unique
    | Mut witness -> Mut (S.mutable_reference span witness)

  and dpat (p : A.pat) : B.pat =
    { p = dpat' p.span p.p; span = p.span; typ = dty p.span p.typ }

  and dpat' (span : span) (pat : A.pat') : B.pat' =
    match pat with
    | PWild -> PWild
    | PAscription { typ; typ_span; pat } ->
        PAscription { typ = dty span typ; pat = dpat pat; typ_span }
    | PConstruct { name; args; is_record; is_struct } ->
        PConstruct
          {
            name;
            args = List.map ~f:(dfield_pat span) args;
            is_record;
            is_struct;
          }
    | POr { subpats } -> POr { subpats = List.map ~f:dpat subpats }
    | PArray { args } -> PArray { args = List.map ~f:dpat args }
    | PConstant { lit } -> PConstant { lit }
    | PBinding { mut; mode; var : Local_ident.t; typ; subpat } ->
        PBinding
          {
            mut = dmutability span S.mutable_variable mut;
            mode = dbinding_mode span mode;
            var;
            typ = dty span typ;
            subpat = Option.map ~f:(dpat *** S.as_pattern span) subpat;
          }
    | PDeref { subpat; witness } ->
        PDeref { subpat = dpat subpat; witness = S.reference span witness }

  and dfield_pat (_span : span) (p : A.field_pat) : B.field_pat =
    { field = p.field; pat = dpat p.pat }

  and dbinding_mode (span : span) (binding_mode : A.binding_mode) :
      B.binding_mode =
    match binding_mode with
    | ByValue -> ByValue
    | ByRef (kind, witness) ->
        ByRef (dborrow_kind span kind, S.reference span witness)

  and dsupported_monads (span : span) (m : A.supported_monads) :
      B.supported_monads =
    match m with
    | MException t -> MException (dty span t)
    | MResult t -> MResult (dty span t)
    | MOption -> MOption

  and dexpr (e : A.expr) : B.expr =
    try dexpr_unwrapped e
    with Diagnostics.SpanFreeError.Exn (Data (context, kind)) ->
      let typ : B.ty =
        try dty e.span e.typ
        with Diagnostics.SpanFreeError.Exn (Data (_context, _kind)) ->
          UB.hax_failure_typ
      in
      UB.hax_failure_expr e.span typ (context, kind) (UA.LiftToFullAst.expr e)

  and dexpr_unwrapped (e : A.expr) : B.expr =
    { e = dexpr' e.span e.e; span = e.span; typ = dty e.span e.typ }

  and dexpr' (span : span) (expr : A.expr') : B.expr' =
    match expr with
    | If { cond; then_; else_ } ->
        If
          {
            cond = dexpr cond;
            then_ = dexpr then_;
            else_ = Option.map ~f:dexpr else_;
          }
    | App { f; args; generic_args; impl } ->
        App
          {
            f = dexpr f;
            args = List.map ~f:dexpr args;
            generic_args = List.map ~f:(dgeneric_value span) generic_args;
            impl = Option.map ~f:(dimpl_expr span) impl;
          }
    | Literal lit -> Literal lit
    | Array l -> Array (List.map ~f:dexpr l)
    | Construct { constructor; is_record; is_struct; fields; base } ->
        Construct
          {
            constructor;
            is_record;
            is_struct;
            fields = List.map ~f:(map_snd dexpr) fields;
            base = Option.map ~f:(dexpr *** S.construct_base span) base;
          }
    | Match { scrutinee; arms } ->
        Match { scrutinee = dexpr scrutinee; arms = List.map ~f:darm arms }
    | Let { monadic; lhs; rhs; body } ->
        Let
          {
            monadic =
              Option.map
                ~f:(dsupported_monads span *** S.monadic_binding span)
                monadic;
            lhs = dpat lhs;
            rhs = dexpr rhs;
            body = dexpr body;
          }
    | Block (e, witness) -> Block (dexpr e, S.block span witness)
    | LocalVar local_ident -> LocalVar local_ident
    | GlobalVar global_ident -> GlobalVar global_ident
    | Ascription { e; typ } -> Ascription { e = dexpr e; typ = dty span typ }
    | MacroInvokation { macro; args; witness } ->
        MacroInvokation { macro; args; witness = S.macro span witness }
    | Assign { lhs; e; witness } ->
        Assign
          {
            lhs = dlhs span lhs;
            e = dexpr e;
            witness = S.mutable_variable span witness;
          }
    | Loop { body; kind; state; label; witness } ->
        Loop
          {
            body = dexpr body;
            kind = dloop_kind span kind;
            state = Option.map ~f:(dloop_state span) state;
            label;
            witness = S.loop span witness;
          }
    | Break { e; label; witness } ->
        Break
          {
            e = dexpr e;
            label;
            witness = (S.break span *** S.loop span) witness;
          }
    | Return { e; witness } ->
        Return { e = dexpr e; witness = S.early_exit span witness }
    | QuestionMark { e; return_typ; witness } ->
        QuestionMark
          {
            e = dexpr e;
            return_typ = dty span return_typ;
            witness = S.question_mark span witness;
          }
    | Continue { e; label; witness = w1, w2 } ->
        Continue
          {
            e = Option.map ~f:(S.state_passing_loop span *** dexpr) e;
            label;
            witness = (S.continue span w1, S.loop span w2);
          }
    | Borrow { kind; e; witness } ->
        Borrow
          {
            kind = dborrow_kind span kind;
            e = dexpr e;
            witness = S.reference span witness;
          }
    | EffectAction { action; argument } ->
        EffectAction
          { action = S.monadic_action span action; argument = dexpr argument }
    | AddressOf { mut; e; witness } ->
        AddressOf
          {
            mut = dmutability span S.mutable_pointer mut;
            e = dexpr e;
            witness = S.raw_pointer span witness;
          }
    | Closure { params; body; captures } ->
        Closure
          {
            params = List.map ~f:dpat params;
            body = dexpr body;
            captures = List.map ~f:dexpr captures;
          }

  and dloop_kind (span : span) (k : A.loop_kind) : B.loop_kind =
    match k with
    | UnconditionalLoop -> UnconditionalLoop
    | ForLoop { it; pat; witness } ->
        ForLoop
          { it = dexpr it; pat = dpat pat; witness = S.for_loop span witness }
    | ForIndexLoop { start; end_; var; var_typ; witness } ->
        ForIndexLoop
          {
            start = dexpr start;
            end_ = dexpr end_;
            var;
            var_typ = dty span var_typ;
            witness = S.for_index_loop span witness;
          }

  and dloop_state (span : span) (s : A.loop_state) : B.loop_state =
    {
      init = dexpr s.init;
      bpat = dpat s.bpat;
      witness = S.state_passing_loop span s.witness;
    }

  and darm (a : A.arm) : B.arm = { span = a.span; arm = darm' a.span a.arm }

  and darm' (_span : span) (a : A.arm') : B.arm' =
    { arm_pat = dpat a.arm_pat; body = dexpr a.body }

  and dlhs (span : span) (lhs : A.lhs) : B.lhs =
    match lhs with
    | LhsFieldAccessor { e; field; typ; witness } ->
        LhsFieldAccessor
          {
            e = dlhs span e;
            field;
            typ = dty span typ;
            witness = S.nontrivial_lhs span witness;
          }
    | LhsArrayAccessor { e; index; typ; witness } ->
        LhsArrayAccessor
          {
            e = dlhs span e;
            index = dexpr index;
            typ = dty span typ;
            witness = S.nontrivial_lhs span witness;
          }
    | LhsLocalVar { var; typ } -> LhsLocalVar { var; typ = dty span typ }
    | LhsArbitraryExpr { e; witness } ->
        LhsArbitraryExpr { e = dexpr e; witness = S.arbitrary_lhs span witness }

  module Item = struct
    (* TODO: remvove span argument *)
    let dgeneric_param _span ({ ident; span; attrs; kind } : A.generic_param) :
        B.generic_param =
      let kind =
        match kind with
        | GPLifetime { witness } ->
            B.GPLifetime { witness = S.lifetime span witness }
        | GPType { default } ->
            GPType { default = Option.map ~f:(dty span) default }
        | GPConst { typ } -> GPConst { typ = dty span typ }
      in
      { ident; span; kind; attrs }

    let dgeneric_constraint (span : span)
        (generic_constraint : A.generic_constraint) : B.generic_constraint =
      match generic_constraint with
      | GCLifetime (lf, witness) -> B.GCLifetime (lf, S.lifetime span witness)
      | GCType { bound; id } -> B.GCType { bound = dtrait_ref span bound; id }

    let dgenerics (span : span) (g : A.generics) : B.generics =
      {
        params = List.map ~f:(dgeneric_param span) g.params;
        constraints = List.map ~f:(dgeneric_constraint span) g.constraints;
      }

    let dparam (span : span) (p : A.param) : B.param =
      {
        pat = dpat p.pat;
        typ = dty (Option.value ~default:span p.typ_span) p.typ;
        typ_span = p.typ_span;
        attrs = p.attrs;
      }

    let dvariant (span : span) (v : A.variant) : B.variant =
      {
        name = v.name;
        arguments = List.map ~f:(map_snd3 @@ dty span) v.arguments;
        is_record = v.is_record;
        attrs = v.attrs;
      }

    let rec dtrait_item' (span : span) (ti : A.trait_item') : B.trait_item' =
      match ti with
      | TIType g -> TIType (List.map ~f:(dtrait_ref span) g)
      | TIFn t -> TIFn (dty span t)

    and dtrait_item (ti : A.trait_item) : B.trait_item =
      {
        ti_span = ti.ti_span;
        ti_generics = dgenerics ti.ti_span ti.ti_generics;
        ti_v = dtrait_item' ti.ti_span ti.ti_v;
        ti_ident = ti.ti_ident;
        ti_attrs = ti.ti_attrs;
      }

    let rec dimpl_item' (span : span) (ii : A.impl_item') : B.impl_item' =
      match ii with
      | IIType g -> IIType (dty span g)
      | IIFn { body; params } ->
          IIFn { body = dexpr body; params = List.map ~f:(dparam span) params }

    and dimpl_item (ii : A.impl_item) : B.impl_item =
      {
        ii_span = ii.ii_span;
        ii_generics = dgenerics ii.ii_span ii.ii_generics;
        ii_v = dimpl_item' ii.ii_span ii.ii_v;
        ii_ident = ii.ii_ident;
        ii_attrs = ii.ii_attrs;
      }

    let rec ditem (i : A.item) : B.item list =
      try ditem_unwrapped i
      with Diagnostics.SpanFreeError.Exn (Data (context, kind)) ->
        let error = Diagnostics.pretty_print_context_kind context kind in
        let cast_item : A.item -> Ast.Full.item = Stdlib.Obj.magic in
        let ast = cast_item i |> Print_rust.pitem_str in
        let msg = error ^ "\nLast available AST for this item:\n\n" ^ ast in
        [ B.make_hax_error_item i.span i.ident msg ]

    and ditem_unwrapped (item : A.item) : B.item list =
      [
        {
          v = ditem' item.span item.v;
          span = item.span;
          ident = item.ident;
          attrs = item.attrs;
        };
      ]

    and ditem' (span : span) (item : A.item') : B.item' =
      match item with
      | Fn { name; generics; body; params } ->
          B.Fn
            {
              name;
              generics = dgenerics span generics;
              body = dexpr body;
              params = List.map ~f:(dparam span) params;
            }
      | Type { name; generics; variants; is_struct } ->
          B.Type
            {
              name;
              generics = dgenerics span generics;
              variants = List.map ~f:(dvariant span) variants;
              is_struct;
            }
      | TyAlias { name; generics; ty } ->
          B.TyAlias
            { name; generics = dgenerics span generics; ty = dty span ty }
      | IMacroInvokation { macro; argument; span; witness } ->
          B.IMacroInvokation
            { macro; argument; span; witness = S.macro span witness }
      | Trait { name; generics; items } ->
          B.Trait
            {
              name;
              generics = dgenerics span generics;
              items = List.map ~f:dtrait_item items;
            }
      | Impl { generics; self_ty; of_trait = trait_id, trait_generics; items }
        ->
          B.Impl
            {
              generics = dgenerics span generics;
              self_ty = dty span self_ty;
              of_trait =
                (trait_id, List.map ~f:(dgeneric_value span) trait_generics);
              items = List.map ~f:dimpl_item items;
            }
      | Alias { name; item } -> B.Alias { name; item }
      | Use { path; is_external; rename } -> B.Use { path; is_external; rename }
      | HaxError e -> B.HaxError e
      | NotImplementedYet -> B.NotImplementedYet

    let ditems = List.concat_map ~f:ditem
  end

  include Item
end

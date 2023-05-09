open Base
open Utils

module Make
    (FA : Features.T)
    (FB : Features.T)
    (S : Features.SUBTYPE.T with module A = FA and module B = FB) =
struct
  open Ast
  module A = Ast.Make (FA)
  module B = Ast.Make (FB)
  module FA = FA

  let dmutability (_span : span) (type a b) (s : a -> b)
      (mutability : a mutability) : b mutability =
    match mutability with Mutable w -> Mutable (s w) | Immutable -> Immutable

  let rec dty (span : span) (ty : A.ty) : B.ty =
    match ty with
    | TBool -> TBool
    | TChar -> TChar
    | TInt k -> TInt k
    | TFloat -> TFloat
    | TStr -> TStr
    | TApp { ident; args } ->
        TApp { ident; args = List.map ~f:(dgeneric_value span) args }
    | TArray { typ; length } -> TArray { typ = dty span typ; length }
    | TSlice { witness; ty } ->
        TSlice { witness = S.slice witness; ty = dty span ty }
    | TRef { witness; typ; mut; region } ->
        TRef
          {
            witness = S.reference witness;
            typ = dty span typ;
            mut = dmutability span S.mutable_reference mut;
            region;
          }
    | TFalse -> TFalse
    | TParam local_ident -> TParam local_ident
    | TArrow (inputs, output) ->
        TArrow (List.map ~f:(dty span) inputs, dty span output)
    | TProjectedAssociatedType string -> TProjectedAssociatedType string
    | TRawPointer { witness } -> TRawPointer { witness = S.raw_pointer witness }

  and dgeneric_value (span : span) (generic_value : A.generic_value) :
      B.generic_value =
    match generic_value with
    | GLifetime { lt; witness } ->
        GLifetime { lt; witness = S.lifetime witness }
    | GType t -> GType (dty span t)
    | GConst c -> GConst c

  let dborrow_kind (_span : span) (borrow_kind : A.borrow_kind) : B.borrow_kind
      =
    match borrow_kind with
    | Shared -> Shared
    | Unique -> Unique
    | Mut witness -> Mut (S.mutable_reference witness)

  let rec dpat (p : A.pat) : B.pat =
    { p = dpat' p.span p.p; span = p.span; typ = dty p.span p.typ }

  and dpat' (span : span) (pat : A.pat') : B.pat' =
    match pat with
    | PWild -> PWild
    | PAscription { typ; typ_span; pat } ->
        PAscription { typ = dty span typ; pat = dpat pat; typ_span }
    | PConstruct { name; args; record } ->
        PConstruct { name; record; args = List.map ~f:(dfield_pat span) args }
    | PArray { args } -> PArray { args = List.map ~f:dpat args }
    | PConstant { lit } -> PConstant { lit }
    | PBinding { mut; mode; var : LocalIdent.t; typ; subpat } ->
        PBinding
          {
            mut = dmutability span S.mutable_variable mut;
            mode = dbinding_mode span mode;
            var;
            typ = dty span typ;
            subpat = Option.map ~f:(dpat *** S.as_pattern) subpat;
          }
    | PDeref { subpat; witness } ->
        PDeref { subpat = dpat subpat; witness = S.reference witness }

  and dfield_pat (_span : span) (p : A.field_pat) : B.field_pat =
    { field = p.field; pat = dpat p.pat }

  and dbinding_mode (span : span) (binding_mode : A.binding_mode) :
      B.binding_mode =
    match binding_mode with
    | ByValue -> ByValue
    | ByRef (kind, witness) ->
        ByRef (dborrow_kind span kind, S.reference witness)

  let rec dexpr (e : A.expr) : B.expr =
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
    | App { f; args } -> App { f = dexpr f; args = List.map ~f:dexpr args }
    | Literal lit -> Literal lit
    | Array l -> Array (List.map ~f:dexpr l)
    | Construct { constructor; constructs_record; fields; base } ->
        Construct
          {
            constructor;
            constructs_record;
            fields = List.map ~f:(map_snd dexpr) fields;
            base = Option.map ~f:dexpr base;
          }
    | Match { scrutinee; arms } ->
        Match { scrutinee = dexpr scrutinee; arms = List.map ~f:darm arms }
    | Let { monadic; lhs; rhs; body } ->
        Let
          {
            monadic = Option.map ~f:(Fn.id *** S.monadic_binding) monadic;
            lhs = dpat lhs;
            rhs = dexpr rhs;
            body = dexpr body;
          }
    | LocalVar local_ident -> LocalVar local_ident
    | GlobalVar global_ident -> GlobalVar global_ident
    | Ascription { e; typ } -> Ascription { e = dexpr e; typ = dty span typ }
    | MacroInvokation { macro; args; witness } ->
        MacroInvokation { macro; args; witness = S.macro witness }
    | Assign { lhs; e; witness } ->
        Assign
          {
            lhs = dlhs span lhs;
            e = dexpr e;
            witness = S.mutable_variable witness;
          }
    | Loop { body; kind; state; label; witness } ->
        Loop
          {
            body = dexpr body;
            kind = dloop_kind span kind;
            state = Option.map ~f:(dloop_state span) state;
            label;
            witness = S.loop witness;
          }
    | Break { e; label; witness } ->
        Break { e = dexpr e; label; witness = S.loop witness }
    | Return { e; witness } ->
        Return { e = dexpr e; witness = S.early_exit witness }
    | Continue { e; label; witness = w1, w2 } ->
        Continue
          {
            e = Option.map ~f:(S.state_passing_loop *** dexpr) e;
            label;
            witness = (S.continue w1, S.loop w2);
          }
    | Borrow { kind; e; witness } ->
        Borrow
          {
            kind = dborrow_kind span kind;
            e = dexpr e;
            witness = S.reference witness;
          }
    | EffectAction { action; argument } ->
        EffectAction
          { action = S.monadic_action action; argument = dexpr argument }
    | AddressOf { mut; e; witness } ->
        AddressOf
          {
            mut = dmutability span S.mutable_pointer mut;
            e = dexpr e;
            witness = S.raw_pointer witness;
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
    | ForLoop { start; end_; var; var_typ; witness } ->
        ForLoop
          {
            start = dexpr start;
            end_ = dexpr end_;
            var;
            var_typ = dty span var_typ;
            witness = S.for_loop witness;
          }

  and dloop_state (_span : span) (s : A.loop_state) : B.loop_state =
    {
      init = dexpr s.init;
      bpat = dpat s.bpat;
      witness = S.state_passing_loop s.witness;
    }

  and darm (a : A.arm) : B.arm = { span = a.span; arm = darm' a.span a.arm }

  and darm' (_span : span) (a : A.arm') : B.arm' =
    { pat = dpat a.pat; body = dexpr a.body }

  and dlhs (span : span) (lhs : A.lhs) : B.lhs =
    match lhs with
    | LhsFieldAccessor { e; field; typ } ->
        LhsFieldAccessor { e = dlhs span e; field; typ = dty span typ }
    | LhsArrayAccessor { e; index; typ } ->
        LhsArrayAccessor
          { e = dlhs span e; index = dexpr index; typ = dty span typ }
    | LhsLocalVar { var; typ } -> LhsLocalVar { var; typ = dty span typ }
    | LhsArbitraryExpr { e; witness } ->
        LhsArbitraryExpr { e = dexpr e; witness = S.arbitrary_lhs witness }

  module Item = struct
    let dtrait_ref (span : span) (r : A.trait_ref) : B.trait_ref =
      {
        trait = r.trait;
        args = List.map ~f:(dgeneric_value span) r.args;
        bindings = r.bindings;
      }

    let dgeneric_param (span : span) (generic_param : A.generic_param) :
        B.generic_param =
      match generic_param with
      | GPLifetime { ident; witness } ->
          GPLifetime { ident; witness = S.lifetime witness }
      | GPType { ident; default } ->
          GPType { ident; default = Option.map ~f:(dty span) default }
      | GPConst { ident; typ } -> GPConst { ident; typ = dty span typ }

    let dgeneric_constraint (span : span)
        (generic_constraint : A.generic_constraint) : B.generic_constraint =
      match generic_constraint with
      | GCLifetime (lf, witness) -> B.GCLifetime (lf, S.lifetime witness)
      | GCType { typ; implements } ->
          B.GCType
            { typ = dty span typ; implements = dtrait_ref span implements }

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
      }

    let dvariant (span : span) (v : A.variant) : B.variant =
      {
        name = v.name;
        arguments = List.map ~f:(map_snd @@ dty span) v.arguments;
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
        ti_name = ti.ti_name;
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
        ii_name = ii.ii_name;
      }

    let rec ditem (item : A.item) : B.item list =
      [
        {
          v = ditem' item.span item.v;
          span = item.span;
          parent_namespace = item.parent_namespace;
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
      | Type { name; generics; variants; record } ->
          B.Type
            {
              name;
              generics = dgenerics span generics;
              variants = List.map ~f:(dvariant span) variants;
              record;
            }
      | TyAlias { name; generics; ty } ->
          B.TyAlias
            { name; generics = dgenerics span generics; ty = dty span ty }
      | IMacroInvokation { macro; argument; span; witness } ->
          B.IMacroInvokation
            { macro; argument; span; witness = S.macro witness }
      | Trait { name; generics; items } ->
          B.Trait
            {
              name;
              generics = dgenerics span generics;
              items = List.map ~f:dtrait_item items;
            }
      | Impl { generics; self_ty; of_trait; items } ->
          B.Impl
            {
              generics = dgenerics span generics;
              self_ty = dty span self_ty;
              of_trait =
                Option.map
                  ~f:(Fn.id *** List.map ~f:(dgeneric_value span))
                  of_trait;
              items = List.map ~f:dimpl_item items;
            }
      | Use { path; is_external; rename } -> B.Use { path; is_external; rename }
      | NotImplementedYet -> B.NotImplementedYet
  end

  include Item
end

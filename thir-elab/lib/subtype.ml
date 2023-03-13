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

  let dmutability (type a b) (s : a -> b) (mutability : a mutability) :
      b mutability =
    match mutability with Mutable w -> Mutable (s w) | Immutable -> Immutable

  let rec dty (ty : A.ty) : B.ty =
    match ty with
    | TBool -> TBool
    | TChar -> TChar
    | TInt k -> TInt k
    | TFloat -> TFloat
    | TStr -> TStr
    | TApp { ident; args } ->
        TApp { ident; args = List.map ~f:dgeneric_value args }
    | TArray { typ; length } -> TArray { typ = dty typ; length }
    | TSlice { witness; ty } ->
        TSlice { witness = S.slice witness; ty = dty ty }
    | TRef { witness; typ; mut; region } ->
        TRef
          {
            witness = S.reference witness;
            typ = dty typ;
            mut = dmutability S.mutable_reference mut;
            region;
          }
    | TFalse -> TFalse
    | TParam local_ident -> TParam local_ident
    | TArrow (inputs, output) -> TArrow (List.map ~f:dty inputs, dty output)
    | TProjectedAssociatedType string -> TProjectedAssociatedType string
    | TRawPointer { witness } -> TRawPointer { witness = S.raw_pointer witness }

  and dgeneric_value (generic_value : A.generic_value) : B.generic_value =
    match generic_value with
    | GLifetime { lt; witness } ->
        GLifetime { lt; witness = S.lifetime witness }
    | GType t -> GType (dty t)
    | GConst c -> GConst c

  let dborrow_kind (borrow_kind : A.borrow_kind) : B.borrow_kind =
    match borrow_kind with
    | Shared -> Shared
    | Unique -> Unique
    | Mut witness -> Mut (S.mutable_reference witness)

  let rec dpat (p : A.pat) : B.pat =
    { p = dpat' p.p; span = p.span; typ = dty p.typ }

  and dpat' (pat : A.pat') : B.pat' =
    match pat with
    | PWild -> PWild
    | PAscription { typ; typ_span; pat } ->
        PAscription { typ = dty typ; pat = dpat pat; typ_span }
    | PConstruct { name; args; record } ->
        PConstruct { name; record; args = List.map ~f:dfield_pat args }
    | PArray { args } -> PArray { args = List.map ~f:dpat args }
    | PConstant { lit } -> PConstant { lit }
    | PBinding { mut; mode; var : LocalIdent.t; typ; subpat } ->
        PBinding
          {
            mut = dmutability S.mutable_variable mut;
            mode = dbinding_mode mode;
            var;
            typ = dty typ;
            subpat = Option.map ~f:(dpat *** S.as_pattern) subpat;
          }
    | PDeref { subpat } -> (dpat subpat).p

  and dfield_pat (p : A.field_pat) : B.field_pat =
    { field = p.field; pat = dpat p.pat }

  and dbinding_mode (binding_mode : A.binding_mode) : B.binding_mode =
    match binding_mode with
    | ByValue -> ByValue
    | ByRef (kind, witness) -> ByRef (dborrow_kind kind, S.reference witness)

  let rec dexpr (e : A.expr) : B.expr =
    { e = dexpr' e.e; span = e.span; typ = dty e.typ }

  and dexpr' (expr : A.expr') : B.expr' =
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
    | Ascription { e; typ } -> Ascription { e = dexpr e; typ = dty typ }
    | MacroInvokation { macro; args; witness } ->
        MacroInvokation { macro; args; witness = S.macro witness }
    | Assign { lhs; e; witness } ->
        Assign
          { lhs = dlhs lhs; e = dexpr e; witness = S.mutable_variable witness }
    | Loop { body; label; witness } ->
        Loop { body = dexpr body; label; witness = S.loop witness }
    | ForLoop { start; end_; var; body; label; witness } ->
        ForLoop
          {
            start = dexpr start;
            end_ = dexpr end_;
            var;
            body = dexpr body;
            label;
            witness = S.for_loop witness;
          }
    | Break { e; label; witness } ->
        Break { e = dexpr e; label; witness = S.loop witness }
    | Return { e; witness } ->
        Return { e = dexpr e; witness = S.early_exit witness }
    | Continue { label; witness = w1, w2 } ->
        Continue { label; witness = (S.continue w1, S.loop w2) }
    | Borrow { kind; e; witness } ->
        Borrow
          {
            kind = dborrow_kind kind;
            e = dexpr e;
            witness = S.reference witness;
          }
    | MonadicAction { action; argument } ->
        MonadicAction
          { action = S.monadic_action action; argument = dexpr argument }
    | AddressOf { mut; e; witness } ->
        AddressOf
          {
            mut = dmutability S.mutable_pointer mut;
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

  and darm (a : A.arm) : B.arm = { span = a.span; arm = darm' a.arm }
  and darm' (a : A.arm') : B.arm' = { pat = dpat a.pat; body = dexpr a.body }

  and dlhs (lhs : A.lhs) : B.lhs =
    match lhs with
    | LhsFieldAccessor { e; field; typ } ->
        LhsFieldAccessor { e = dlhs e; field; typ = dty typ }
    | LhsArrayAccessor { e; index; typ } ->
        LhsArrayAccessor { e = dlhs e; index = dexpr index; typ = dty typ }
    | LhsLocalVar { var; typ } -> LhsLocalVar { var; typ = dty typ }
    | LhsArbitraryExpr { e; witness } ->
        LhsArbitraryExpr { e = dexpr e; witness = S.arbitrary_lhs witness }

  module Item = struct
    let dtrait_ref (r : A.trait_ref) : B.trait_ref =
      {
        trait = r.trait;
        args = List.map ~f:dgeneric_value r.args;
        bindings = r.bindings;
      }

    let dgeneric_param (generic_param : A.generic_param) : B.generic_param =
      match generic_param with
      | GPLifetime { ident; witness } ->
          GPLifetime { ident; witness = S.lifetime witness }
      | GPType { ident; default } ->
          GPType { ident; default = Option.map ~f:dty default }
      | GPConst { ident; typ } -> GPConst { ident; typ = dty typ }

    let dgeneric_constraint (generic_constraint : A.generic_constraint) :
        B.generic_constraint =
      match generic_constraint with
      | GCLifetime (lf, witness) -> B.GCLifetime (lf, S.lifetime witness)
      | GCType { typ; implements } ->
          B.GCType { typ = dty typ; implements = dtrait_ref implements }

    let dgenerics (g : A.generics) : B.generics =
      {
        params = List.map ~f:dgeneric_param g.params;
        constraints = List.map ~f:dgeneric_constraint g.constraints;
      }

    let dparam (p : A.param) : B.param =
      { pat = dpat p.pat; typ = dty p.typ; typ_span = p.typ_span }

    let dvariant (v : A.variant) : B.variant =
      { name = v.name; arguments = List.map ~f:(map_snd dty) v.arguments }

    let rec ditem (item : A.item) : B.item list =
      [
        {
          v = ditem' item.v;
          span = item.span;
          parent_namespace = item.parent_namespace;
        };
      ]

    and ditem' (item : A.item') : B.item' =
      match item with
      | Fn { name; generics; body; params } ->
          B.Fn
            {
              name;
              generics = dgenerics generics;
              body = dexpr body;
              params = List.map ~f:dparam params;
            }
      | Type { name; generics; variants; record } ->
          B.Type
            {
              name;
              generics = dgenerics generics;
              variants = List.map ~f:dvariant variants;
              record;
            }
      | TyAlias { name; generics; ty } ->
          B.TyAlias { name; generics = dgenerics generics; ty = dty ty }
      | IMacroInvokation { macro; argument; span; witness } ->
          B.IMacroInvokation
            { macro; argument; span; witness = S.macro witness }
      | NotImplementedYet -> B.NotImplementedYet
  end

  include Item
end

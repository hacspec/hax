open Base
open Utils

module Make (F : Features.T) = struct
  open Ast

  module F' = struct
    include F
  end

  module A = Ast.Make (F)
  module B = Ast.Make (F')

  let rec dty (t : A.ty) : B.ty =
    match t with
    | TBool -> TBool
    | TChar -> TChar
    | TInt k -> TInt k
    | TFloat -> TFloat
    | TStr -> TStr
    | TApp { ident; args } ->
        TApp { ident; args = List.map ~f:dgeneric_value args }
    | TArray { typ; length } -> TArray { typ = dty typ; length }
    | TSlice { witness; ty } -> TSlice { witness; ty = dty ty }
    | TRef { witness; typ; mut; region } ->
        TRef { witness; typ = dty typ; mut; region }
    | TFalse -> TFalse
    | TParam local_ident -> TParam local_ident
    | TArrow (inputs, output) -> TArrow (List.map ~f:dty inputs, dty output)
    | TProjectedAssociatedType string -> TProjectedAssociatedType string
    | TRawPointer { witness } -> TRawPointer { witness }

  and dgeneric_value (g : A.generic_value) : B.generic_value =
    match g with
    | GLifetime { lt; witness } -> GLifetime { lt; witness }
    | GType t -> GType (dty t)
    | GConst c -> GConst c

  let dborrow_kind (k : A.borrow_kind) : B.borrow_kind =
    match k with
    | Shared -> Shared
    | Unique -> Unique
    | Mut witness -> Mut witness

  let rec dpat (p : A.pat) : B.pat =
    { p = dpat' p.p; span = p.span; typ = dty p.typ }

  and dpat' (p : A.pat') : B.pat' =
    match p with
    | PWild -> PWild
    | PAscription { typ; typ_span; pat } ->
        PAscription { typ = dty typ; typ_span; pat = dpat pat }
    | PConstruct { name; args; record } ->
        PConstruct { name; record; args = List.map ~f:dfield_pat args }
    | PArray { args } -> PArray { args = List.map ~f:dpat args }
    | PConstant { lit } -> PConstant { lit }
    | PBinding { mut; mode; var : LocalIdent.t; typ; subpat } ->
        PBinding
          {
            mut;
            mode = ByValue;
            var;
            typ = dty typ;
            subpat = Option.map ~f:(dpat *** Fn.id) subpat;
          }
    | PDeref { subpat } -> (dpat subpat).p

  and dfield_pat (p : A.field_pat) : B.field_pat =
    { field = p.field; pat = dpat p.pat }

  and dbinding_mode (m : A.binding_mode) : B.binding_mode =
    match m with
    | ByValue -> ByValue
    | ByRef (kind, witness) -> ByRef (dborrow_kind kind, witness)

  let rec dexpr (e : A.expr) : B.expr =
    { e = dexpr' e.e; span = e.span; typ = dty e.typ }

  and dexpr' (e : A.expr') : B.expr' =
    match e with
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
        Let { monadic; lhs = dpat lhs; rhs = dexpr rhs; body = dexpr body }
    | LocalVar local_ident -> LocalVar local_ident
    | GlobalVar global_ident -> GlobalVar global_ident
    | Ascription { e; typ } -> Ascription { e = dexpr e; typ = dty typ }
    | MacroInvokation { macro; args; witness } ->
        MacroInvokation { macro; args; witness }
    | Assign { lhs; e; witness } ->
        Assign { lhs = dlhs lhs; e = dexpr e; witness }
    | Loop { body; label; witness } ->
        Loop { body = dexpr body; label; witness }
    | Break { e; label; witness } -> Break { e = dexpr e; label; witness }
    | Return { e; witness } -> Return { e = dexpr e; witness }
    | Continue { label; witness } -> Continue { label; witness }
    | Borrow { kind; e; witness } ->
        Borrow { kind = dborrow_kind kind; e = dexpr e; witness }
    | MonadicAction { action; argument } ->
        MonadicAction { action; argument = dexpr argument }
    | AddressOf { mut; e; witness } -> AddressOf { mut; e = dexpr e; witness }
    | Closure { params; body; captures } ->
        Closure
          {
            params = List.map ~f:dpat params;
            body = dexpr body;
            captures = List.map ~f:dexpr captures;
          }

  and darm (a : A.arm) : B.arm = B.{ span = a.span; arm = darm' a.arm }
  and darm' (a : A.arm') : B.arm' = { pat = dpat a.pat; body = dexpr a.body }

  and dlhs (e : A.lhs) : B.lhs =
    match e with
    | FieldAccessor { e; field } -> FieldAccessor { e = dexpr e; field }
    | ArrayAccessor { e; index } ->
        ArrayAccessor { e = dexpr e; index = dexpr index }
    | LhsLocalVar id -> LhsLocalVar id

  (* let ditem (i: A.item): B.item = i *)
end

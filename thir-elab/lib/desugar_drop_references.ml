open Base
open Utils

module%inlined_contents Make
    (F : Features.T
           with type raw_pointer = Features.off
            and type mutable_reference = Features.off) =
struct
  open Ast
  module FA = F

  module FB = struct
    include F
    include Features.Off.Mutable_pointer
    include Features.Off.Lifetime
    include Features.Off.Reference
  end

  module A = Ast.Make (F)
  module B = Ast.Make (FB)

  module S = struct
    include Features.SUBTYPE.Id
  end

  let rec dty (t : A.ty) : B.ty =
    match t with
    | TBool -> TBool
    | TChar -> TChar
    | TInt k -> TInt k
    | TFloat -> TFloat
    | TStr -> TStr
    | TApp { ident; args } ->
        TApp { ident; args = List.filter_map ~f:dgeneric_value args }
    | TArray { typ; length } -> TArray { typ = dty typ; length }
    | TSlice { witness; ty } -> TSlice { witness; ty = dty ty }
    | TRef { witness; typ; mut = Immutable as mut; region } -> dty typ
    | TFalse -> TFalse
    | TParam local_ident -> TParam local_ident
    | TArrow (inputs, output) -> TArrow (List.map ~f:dty inputs, dty output)
    | TProjectedAssociatedType string -> TProjectedAssociatedType string
    | _ -> .

  and dgeneric_value (g : A.generic_value) : B.generic_value option =
    match g with
    | GLifetime _ -> None
    | GType t -> Some (GType (dty t))
    | GConst c -> Some (GConst c)

  (* let test = *)
  (*   match%auto_arms 1 with *)
  (*   | OneCase -> 0 *)

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
            subpat = Option.map ~f:(fun (p, as_pat) -> (dpat p, as_pat)) subpat;
          }
    | PDeref { subpat } -> (dpat subpat).p

  and dfield_pat (p : A.field_pat) : B.field_pat =
    { field = p.field; pat = dpat p.pat }

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
    | App { f = { e = GlobalVar (`Primitive (Box | Deref)) }; args = [ arg ] }
      ->
        (dexpr arg).e
    | App { f; args } -> App { f = dexpr f; args = List.map ~f:dexpr args }
    | Literal lit -> Literal lit
    | Array l -> Array (List.map ~f:dexpr l)
    | Construct { constructor; constructs_record; fields; base } ->
        Construct
          {
            constructor;
            constructs_record;
            fields = List.map ~f:(fun (i, e) -> (i, dexpr e)) fields;
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
    | [%inline_arms Loop + ForLoop] -> auto
    | Break { e; label; witness } -> Break { e = dexpr e; label; witness }
    | Return { e; witness } -> Return { e = dexpr e; witness }
    | Continue { label; witness } -> Continue { label; witness }
    | Borrow { kind; e; witness } -> (dexpr e).e
    | MonadicAction { action; argument } ->
        MonadicAction { action; argument = dexpr argument }
    | Closure { params; body; captures } ->
        Closure
          {
            params = List.map ~f:dpat params;
            body = dexpr body;
            captures = List.map ~f:dexpr captures;
          }
    | _ -> .

  and darm (a : A.arm) : B.arm = { span = a.span; arm = darm' a.arm }
  and darm' (a : A.arm') : B.arm' = { pat = dpat a.pat; body = dexpr a.body }

  and dlhs (e : A.lhs) : B.lhs =
    match e with
    | FieldAccessor { e; field } -> FieldAccessor { e = dexpr e; field }
    | ArrayAccessor { e; index } ->
        ArrayAccessor { e = dexpr e; index = dexpr index }
    | LhsLocalVar id -> LhsLocalVar id

  let dtrait_ref (r : A.trait_ref) : B.trait_ref =
    {
      trait = r.trait;
      args = List.filter_map ~f:dgeneric_value r.args;
      bindings = r.bindings;
    }

  let dgeneric_param (p : A.generic_param) : B.generic_param option =
    match p with
    | GPLifetime { ident; witness } -> None
    | GPType { ident; default } ->
        Some (GPType { ident; default = Option.map ~f:dty default })
    | GPConst { ident; typ } -> Some (GPConst { ident; typ = dty typ })

  let dgeneric_constraint (p : A.generic_constraint) :
      B.generic_constraint option =
    match p with
    | GCLifetime (lf, witness) -> None
    | GCType { typ; implements } ->
        Some (B.GCType { typ = dty typ; implements = dtrait_ref implements })

  let dgenerics (g : A.generics) : B.generics =
    {
      params = List.filter_map ~f:dgeneric_param g.params;
      constraints = List.filter_map ~f:dgeneric_constraint g.constraints;
    }

  let dparam (p : A.param) : B.param =
    { pat = dpat p.pat; typ = dty p.typ; typ_span = p.typ_span }

  let dvariant (v : A.variant) : B.variant =
    { name = v.name; arguments = List.map ~f:(map_snd dty) v.arguments }

  let ditem (item : A.item) : B.item =
    let v =
      match item.v with
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
      | NotImplementedYet -> B.NotImplementedYet
    in
    { v; span = item.span }

  let metadata = Desugar_utils.Metadata.make "DropReferences"
end
[@@add "subtype.ml"]

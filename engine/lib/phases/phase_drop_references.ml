open Base
open Utils

module%inlined_contents Make
    (F : Features.T
           with type raw_pointer = Features.Off.raw_pointer
            and type mutable_reference = Features.Off.mutable_reference) =
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
  include Phase_utils.NoError

  module S = struct
    include Features.SUBTYPE.Id
  end

  include Phase_utils.DefaultError

  let rec dty (span : span) (t : A.ty) : B.ty =
    match t with
    | [%inline_arms "dty.*" - TApp - TRef] -> auto
    | TApp { ident; args } ->
        TApp { ident; args = List.filter_map ~f:(dgeneric_value span) args }
    | TRef { witness; typ; mut = Immutable as mut; region } -> dty span typ
    | TRef _ -> .

  and dgeneric_value (span : span) (g : A.generic_value) :
      B.generic_value option =
    match g with
    | GLifetime _ -> None
    | GType t -> Some (GType (dty span t))
    | GConst c -> Some (GConst c)

  let rec dpat = [%inline_body dpat]

  and dpat' (span : span) (p : A.pat') : B.pat' =
    match p with
    | [%inline_arms "dpat'.*" - PBinding - PDeref] -> auto
    | PBinding { mut; mode; var : LocalIdent.t; typ; subpat } ->
        PBinding
          {
            mut;
            mode = ByValue;
            var;
            typ = dty span typ;
            subpat = Option.map ~f:(fun (p, as_pat) -> (dpat p, as_pat)) subpat;
          }
    | PDeref { subpat } -> (dpat subpat).p

  and dfield_pat = [%inline_body dfield_pat]

  let rec dexpr = [%inline_body dexpr]

  and dexpr' (span : span) (e : A.expr') : B.expr' =
    match e with
    | [%inline_arms If + Literal + Array] -> auto
    | App { f = { e = GlobalVar (`Primitive (Box | Deref)) }; args = [ arg ] }
      ->
        (dexpr arg).e
    | App { f; args } -> App { f = dexpr f; args = List.map ~f:dexpr args }
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
    | Ascription { e = e'; typ } ->
        Ascription { e = dexpr e'; typ = dty span typ }
    | MacroInvokation { macro; args; witness } ->
        MacroInvokation { macro; args; witness }
    | Assign { lhs; e; witness } ->
        Assign { lhs = dlhs span lhs; e = dexpr e; witness }
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
  and dlhs = [%inline_body dlhs]

  let dtrait_ref (span : span) (r : A.trait_ref) : B.trait_ref =
    {
      trait = r.trait;
      args = List.filter_map ~f:(dgeneric_value span) r.args;
      bindings = r.bindings;
    }

  let dgeneric_param (span : span) (p : A.generic_param) :
      B.generic_param option =
    match p with
    | GPLifetime { ident; witness } -> None
    | GPType { ident; default } ->
        Some (GPType { ident; default = Option.map ~f:(dty span) default })
    | GPConst { ident; typ } -> Some (GPConst { ident; typ = dty span typ })

  let dgeneric_constraint (span : span) (p : A.generic_constraint) :
      B.generic_constraint option =
    match p with
    | GCLifetime (lf, witness) -> None
    | GCType { typ; implements } ->
        Some
          (B.GCType
             { typ = dty span typ; implements = dtrait_ref span implements })

  let dgenerics (span : span) (g : A.generics) : B.generics =
    {
      params = List.filter_map ~f:(dgeneric_param span) g.params;
      constraints = List.filter_map ~f:(dgeneric_constraint span) g.constraints;
    }

  (* [%%inline_defs *)
  (* "Item.*" - dtrait_ref - dgeneric_param - dgeneric_constraint - dgenerics] *)
  [%%inline_defs dparam + dvariant + dtrait_item + dimpl_item]

  let rec ditem = [%inline_body ditem]

  and ditem' (span : span) (item : A.item') : B.item' =
    match item with
    | [%inline_arms "ditem'.*" - Impl] -> auto
    | Impl { generics; self_ty; of_trait; items } ->
        B.Impl
          {
            generics = dgenerics span generics;
            self_ty = dty span self_ty;
            of_trait =
              Option.map
                ~f:(Fn.id *** List.filter_map ~f:(dgeneric_value span))
                of_trait;
            items = List.map ~f:dimpl_item items;
          }

  let metadata = Phase_utils.Metadata.make DropReferences
end
[@@add "../subtype.ml"]

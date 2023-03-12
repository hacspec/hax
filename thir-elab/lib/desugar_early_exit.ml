open Base
open Utils

module%inlined_contents Make
    (FA : Features.T
            with type mutable_reference = Features.Off.mutable_reference
             and type mutable_pointer = Features.Off.mutable_pointer
             and type raw_pointer = Features.Off.raw_pointer
             and type continue = Features.Off.continue
            (* and type monadic = Features.Off.monadic *)
             and type mutable_variable = Features.Off.mutable_variable
             and type loop = Features.Off.loop) =
struct
  open Ast

  module FB = struct
    include FA
    include Features.Off.Early_exit
  end

  module FA = FA
  module A = Ast.Make (FA)
  module B = Ast.Make (FB)
  module S = Features.SUBTYPE.Id

  (* let dmutability (type a b) (s : a -> b) (mutability : a mutability) : b mutability = *)
  (*   [%def_match mutability] *)

  (* let rec dty (ty : A.ty) : B.ty = *)
  (*   [%def_match ty] *)

  (* and dgeneric_value (generic_value: A.generic_value) : B.generic_value = *)
  (*   [%def_match generic_value] *)

  (* let dborrow_kind (borrow_kind : A.borrow_kind) : B.borrow_kind = *)
  (*   [%def_match borrow_kind] *)

  [%%inline_defs dmutability + dty + dborrow_kind + dpat]
  (* let rec dpat (p : A.pat) : B.pat = *)
  (*   { p = dpat' p.p; span = p.span; typ = dty p.typ } *)

  (* and dpat' (pat: A.pat') : B.pat' = *)
  (*   [%def_match pat] *)

  (* and dfield_pat (p : A.field_pat) : B.field_pat = *)
  (*   { field = p.field; pat = dpat p.pat } *)

  (* and dbinding_mode (binding_mode : A.binding_mode) : B.binding_mode = *)
  (*   [%def_match binding_mode] *)

  (* type ctx = { return_type : B.ty }   *)

  (* module Result = struct *)
  (*   type t = Pure of B.expr *)
  (*          | EarlyReturn of { e : B.expr } *)

  (*   let pure (e : A.expr) (e' : B.expr') : t = *)
  (*     Pure { span = e.span; e = e'; typ = dty e.typ } *)

  (*   let seq (l : t) (f : B.expr -> B.expr) : t = failwith "x" *)
  (* end *)

  let rec dexpr (e : A.expr) : B.expr =
    { e = dexpr' e.e; span = e.span; typ = dty e.typ }

  and dexpr' (e : A.expr') : B.expr' =
    match e with
    | Return _ -> failwith "todo"
    | [%inline_arms "dexpr'.*" - Return] -> xx
    | _ -> failwith "todo"

  and darm (a : A.arm) : B.arm = { span = a.span; arm = darm' a.arm }
  and darm' (a : A.arm') : B.arm' = { pat = dpat a.pat; body = dexpr a.body }
  and dlhs : A.lhs -> B.lhs = fun x -> Fn.id [%inline_body dlhs] x

  (*   | If { cond; then_; else_ } -> *)
  (*     If { cond = dexpr cond; *)
  (*          then_ = dexpr then_; *)
  (*          else_ = Option.map ~f:dexpr else_ *)
  (*        } *)
  (*   | App { f; args } -> *)
  (*     App { f = dexpr f; args = List.map ~f:dexpr args } *)
  (*   | Literal lit -> Literal lit *)
  (*   | Array l -> Array (List.map ~f:dexpr l) *)
  (*   | Construct { constructor *)
  (*               ; constructs_record *)
  (*               ; fields *)
  (*               ; base *)
  (*               } *)
  (*       -> Construct { constructor *)
  (*                    ; constructs_record *)
  (*                    ; fields = List.map ~f:(map_snd dexpr) fields *)
  (*                    ; base = Option.map ~f:dexpr base *)
  (*                    } *)
  (*   | Match { scrutinee; arms } -> *)
  (*     Match { scrutinee = dexpr scrutinee; arms = List.map ~f:darm arms } *)
  (*   | Let { lhs; rhs; body } *)
  (*     -> Let { lhs = dpat lhs; rhs = dexpr rhs; body = dexpr body } *)
  (*   | LocalVar local_ident -> LocalVar local_ident *)
  (*   | GlobalVar global_ident -> GlobalVar global_ident *)
  (*   | Ascription { e; typ } -> Ascription { e = dexpr e; typ = dty typ } *)
  (*   | MacroInvokation { macro; args; witness } -> *)
  (*     MacroInvokation { macro; args; witness = witness } *)
  (*   | Assign { lhs; e; witness } -> . *)
  (*   | Loop { body; label; witness } -> . *)
  (*   | Break { e; label; witness } -> . *)
  (*   | Return { e; witness } -> *)
  (*     failwith "TODO return" *)
  (*   | Continue { label; witness = (w1, w2) } -> . *)
  (*   | Borrow { kind; e; witness } -> Borrow {kind = dborrow_kind kind; e = dexpr e; witness} *)
  (*   | MonadicNode { witness } -> MonadicNode { witness } *)
  (*   | AddressOf { mut; e; witness } -> AddressOf { *)
  (*       mut = dmutability S.mutable_pointer mut *)
  (*     ; e = dexpr e *)
  (*     ; witness = S.raw_pointer witness *)
  (*     } *)
  (*   | Closure { params; body; captures } -> Closure { *)
  (*       params = List.map ~f:dpat params; *)
  (*       body = dexpr body; *)
  (*       captures = List.map ~f:dexpr captures *)
  (*     } *)
  (* and darm (a: A.arm): B.arm = *)
  (*   {span = a.span; arm = darm' a.arm } *)
  (* and darm' (a: A.arm'): B.arm' = *)
  (*   { pat = dpat a.pat; body = dexpr a.body } *)
  (* and dlhs (e: A.lhs): B.lhs = *)
  (*   match e with *)
  (*   | FieldAccessor { e; field } -> FieldAccessor { e = dexpr e; field } *)
  (*   | ArrayAccessor { e; index } -> ArrayAccessor { e = dexpr e; index = dexpr index } *)
  (*   | LhsLocalVar id -> LhsLocalVar id *)

  (*
  let dtrait_ref (r: A.trait_ref): B.trait_ref
    = {
      trait = r.trait;
      args = List.map ~f:dgeneric_value r.args;
      bindings = r.bindings
    }

  let dgeneric_param (p: A.generic_param): B.generic_param
    = match p with
    | Lifetime {ident; witness} -> Lifetime {ident; witness = S.lifetime witness}
    | Type {ident; default} -> Type {ident; default = Option.map ~f:dty default}
    | Const {ident; typ} -> Const {ident; typ = dty typ}

  let dgeneric_constraint (p: A.generic_constraint): B.generic_constraint
    = match p with
    | Lifetime (lf, witness) -> B.Lifetime (lf, S.lifetime witness)
    | Type {typ; implements} -> B.Type {
        typ = dty typ;
        implements = dtrait_ref implements
      }

  let dgenerics (g: A.generics): B.generics
    = { params = List.map ~f:dgeneric_param g.params
      ; constraints = List.map ~f:dgeneric_constraint g.constraints }

  let dparam (p: A.param): B.param
    = { pat = dpat p.pat
      ; typ = dty p.typ
      ; typ_span = p.typ_span }

  let dvariant (v: A.variant): B.variant
    = { name = v.name
      ; arguments = List.map ~f:(map_snd dty) v.arguments }
      
  let ditem (item: A.item): B.item
    = let v = match item.v with
      | Fn {name; generics; body; params} ->
          B.Fn {
              name;
              generics = dgenerics generics;
              body = dexpr body;
              params = List.map ~f:dparam params
            }
      | Type {name; generics; variants; record} ->
         B.Type {
             name;
             generics = dgenerics generics;
             variants = List.map ~f:dvariant variants;
             record
           }
      | TyAlias {name; generics; ty} ->
         B.TyAlias {name; generics = dgenerics generics; ty = dty ty}
      | NotImplementedYet -> B.NotImplementedYet
      in {v; span = item.span}

           *)
end
[@@add "subtype.ml"]

open Base
open Ast
open Ast.Make(Features.FStar)
open PPrint
open Utils
module F = struct
  module Util = FStar_Parser_Util
  module AST = FStar_Parser_AST
  module Const = FStar_Const
  module Range = FStar_Compiler_Range
  module Char = FStar_Char
  module Ident = FStar_Ident
  let dummyRange = Range.dummyRange
  let id ident = Ident.mk_ident (ident, dummyRange)
  let lid path =
    let init, last = List.(drop_last_exn path, last_exn path) in
    let capitalize_first_letter s =
      let first, rest = String.(prefix s 1, drop_prefix s 1) in
      String.uppercase first ^ rest
    in
    let init = List.map ~f:capitalize_first_letter init in
    let path = init @ [last] in
    Ident.lid_of_path path dummyRange
  let lid_of_id id = Ident.lid_of_ids [id]
  let term (tm: AST.term') = AST.{ tm; range = dummyRange; level = Expr }
  let decl (d: AST.decl') = AST.{ d; drange = dummyRange; quals = []; attrs = [] }
  let pat (pat: AST.pattern') = AST.{ pat; prange = dummyRange }
  let pat_app name l = pat @@ AST.PatApp (name, l)
  let wild = pat @@ AST.PatWild (None, [])
  let mk_e_app base args = AST.mkApp base (List.map ~f:(fun arg -> arg, AST.Nothing) args) dummyRange
  let mk_e_binder b = AST.{b; brange = dummyRange; blevel = Un; aqual = None; battributes = []}
  let term_of_lid path = term @@ AST.Name (lid path)
  let binder_of_term (t: AST.term): AST.binder
    = mk_e_binder @@ AST.NoName t
  let unit = term AST.(Const Const_unit)
  let mk_e_arrow inputs output =
    term @@ AST.Product (List.map ~f:binder_of_term inputs, output)
  let mk_refined
      (x: string) (typ: AST.term)
      (phi: x:AST.term -> AST.term) =
    let x = id x in
    let x_bd = mk_e_binder @@ AST.Annotated (x, typ) in
    term @@ AST.Refine (x_bd, phi (term @@ AST.Var (lid_of_id x)))
end

let pprim_ident (id: primitive_ident)
  = match id with
  | Box   -> failwith "Box"
  | Deref -> failwith "Box"
  | Cast  -> failwith "Cast"
  | BinOp op -> begin match op with
      | Add    -> F.lid ["Prims"; "op_Addition"]
      | Sub    -> F.lid ["Prims"; "op_Subtraction"]
      | Mul    -> F.lid ["FStar"; "Mul"; "op_Star"]
      | Div    -> F.lid ["Prims"; "op_Division"]
      | Eq     -> F.lid ["Prims"; "op_Equality"]
      | Lt     -> F.lid ["Prims"; "op_LessThan"]
      | Le     -> F.lid ["Prims"; "op_LessThanOrEqual"]
      | Ge     -> F.lid ["Prims"; "op_GreaterThan"]
      | Gt     -> F.lid ["Prims"; "op_GreaterThanOrEqual"]
      | Ne     -> F.lid ["Prims"; "op_disEquality"]
      | Rem    -> failwith "TODO: Rem"
      | BitXor -> failwith "TODO: BitXor"
      | BitAnd -> failwith "TODO: BitAnd"               
      | BitOr  -> failwith "TODO: BitOr"              
      | Shl    -> failwith "TODO: Shl"            
      | Shr    -> failwith "TODO: Shr"            
      | Offset -> failwith "TODO: Offset"               
    end
  | UnOp op -> begin match op with
      | Not -> F.lid ["Prims"; "l_Not"]
      | Neg -> F.lid ["Prims"; "op_Minus"]
    end
  | LogicalOp op -> begin match op with
      | And -> F.lid ["Prims"; "op_AmpAmp"]
      | Or -> F.lid ["Prims"; "op_BarBar"]
    end
  
let rec pliteral (e : literal) =
  match e with
  | String s -> F.Const.Const_string (s, F.dummyRange)
  | Char c -> F.Const.Const_char (Char.to_int c)
  | Int { value } -> F.Const.Const_int (Bigint.to_string value, None)
  | Float _ -> failwith "Float: todo"
  | Bool b -> F.Const.Const_bool b
let rec pglobal_ident (id : global_ident) =
  match id with
  | `Concrete cid -> F.lid (cid.crate::Non_empty_list.to_list cid.path)
  | `Primitive prim_id -> pprim_ident prim_id
  | `Tuple n when n <= 14 -> F.lid ["FStar"; "Pervasives"; "tuple" ^ string_of_int n]
  | `Tuple _ -> failwith "F* doesn't support tuple of size greater than 14"
                    
  | `TupleField (n, size) -> failwith "Cannot appear here"
  | `Projector (`Concrete concrete_ident) -> failwith "Cannot appear here"
  | `Projector (`TupleField n) -> failwith "Cannot appear here"
let rec plocal_ident (e : LocalIdent.t) =
  F.id e.name

let pgeneric_param_name (name: string): string
  = String.lowercase name (* TODO: this is not robust, might produce name clashes *)
    
let rec pty (t : ty) = match t with
  | Bool -> F.term_of_lid ["Prims"; "bool"]
  | Char -> F.term_of_lid ["FStar"; "Char"; "char"]
  | Int k -> F.term_of_lid ["Prims"; "int"] (* todo *)
  | Str -> F.term_of_lid ["Prims"; "string"]
  | False -> F.term_of_lid ["Prims"; "l_False"]
  | App { ident; args } ->
    let base = F.term @@ F.AST.Name (pglobal_ident ident) in
    let args = List.map ~f:pgeneric_value args in
    F.mk_e_app base args
  | Arrow (inputs, output) -> F.mk_e_arrow (List.map ~f:pty inputs) (pty output)
  | Float -> failwith "pty: Float"
  | Array { typ; length } ->
    F.mk_refined
      "x"
      (F.mk_e_app
         (F.term_of_lid ["Prims"; "list"])
         [pty typ]
      ) (fun ~x ->
          let len_of_x = F.mk_e_app  (F.term_of_lid ["FStar";"List";"Tot";"Base";"length"]) [x] in
          let lit = pliteral (Ast.Int {value = Bigint.of_int length; kind = { size = SSize; signedness = Signed }}) in
          let length = F.term @@ F.AST.Const lit in
          let lt = F.term @@ F.AST.Name (pprim_ident @@ BinOp Lt) in
          F.mk_e_app lt [len_of_x; length]
        )
  | Param i -> F.term @@ F.AST.Var (F.lid_of_id @@ plocal_ident {i with name = pgeneric_param_name i.name})
  | ProjectedAssociatedType s -> failwith "proj:assoc:type"
  | _ -> .

and pgeneric_value (g : generic_value) = match g with
  | Type ty -> pty ty
  | Const todo -> failwith "pgeneric_arg: Const"
  | Lifetime _ -> .
    
(* let rec pborrow_kind (e : borrow_kind) = failwith "TODO" *)
let rec ppat (p : pat) = match p.v with
  | Wild -> F.wild
  | PatAscription { typ; pat } ->
    F.pat @@ F.AST.PatAscribed (ppat pat, (pty typ.v, None))
  | Binding {
        mut = Immutable; mode = _; subpat = None;
        var; typ = _ (* we skip type annot here *);
      } ->
    F.pat @@ F.AST.PatVar (plocal_ident var, None, [])
  | PatArray { args } ->
    F.pat @@ F.AST.PatList (List.map ~f:ppat args)
  | Variant { name; args } ->
    let pat_rec = F.pat @@ F.AST.PatRecord (List.map ~f:pfield_pat args) in
    let pat_name = F.pat @@ F.AST.PatName (pglobal_ident name) in
    F.pat_app pat_name [pat_rec]
  | Constant { lit } ->
    F.pat @@ F.AST.PatConst (pliteral lit)
  | Deref { subpat } -> ppat subpat
  | _ -> .
and pfield_pat ({field; pat} : field_pat) =
  pglobal_ident field, ppat pat
      
let rec pexpr (e : expr) = match e.v with
  | Literal e -> F.term @@ F.AST.Const (pliteral e)
  | LocalVar local_ident ->
    F.term @@ F.AST.Var (F.lid_of_id @@ plocal_ident local_ident)
  | GlobalVar global_ident ->
    F.term @@ F.AST.Var (pglobal_ident global_ident)
  | App { f; args } ->
    F.mk_e_app (pexpr f) @@ List.map ~f:pexpr args
  | If { cond; then_; else_ } ->
    F.term @@ F.AST.If (pexpr cond, None, None, pexpr then_, Option.value_map else_ ~default:F.unit ~f:pexpr)
  | Array l ->
    F.AST.mkConsList F.dummyRange (List.map ~f:pexpr l)
  | Let { lhs; rhs; body } ->
      F.term @@ F.AST.Let (NoLetQualifier, [
        None, (ppat lhs, pexpr rhs)
      ], pexpr body)
  | MonadicNode _ -> failwith "monadic node"
  | Match { scrutinee; arms } ->
      F.term @@ F.AST.Match (
        pexpr scrutinee, None, None,
        List.map ~f:parm arms
      )
  | Ascription { e; typ } ->
      F.term @@ F.AST.Ascribed (pexpr e, pty typ, None, false) 
  | Construct { constructs_record = true; constructor; fields; base } ->
      F.term @@ F.AST.Record
           ( Option.map ~f:pexpr base
             , List.map ~f:(fun (f, e) -> pglobal_ident f, pexpr e) fields
           )
  | Construct { constructs_record = false; constructor; fields; base }
    when List.for_all ~f:(fun (f,_) -> match f with
             | `Concrete {path} -> (try let _ = Int.of_string @@ Non_empty_list.last path in true with | _ -> false)
             | _ -> false
           ) fields ->
      assert (Option.is_none base);
      F.mk_e_app (F.term @@ F.AST.Name (pglobal_ident constructor))
      @@ List.map ~f:(snd >> pexpr) fields
  | Construct { constructs_record = false; constructor; fields; base } ->
      let r = F.term @@ F.AST.Record
             ( Option.map ~f:pexpr base
               , List.map ~f:(fun (f, e) -> pglobal_ident f, pexpr e) fields
             )
      in
      F.mk_e_app (F.term @@ F.AST.Name (pglobal_ident constructor)) [r]
  | _-> .
  
and parm ({ v = { pat; body } } : arm) =
  (ppat pat, None, pexpr body)


let doc_to_string: document -> string =
  FStar_Pprint.pretty_string 1.0 (Z.of_int 100)
    
let term_to_string: F.AST.term -> string =
  FStar_Parser_ToDocument.term_to_document >> doc_to_string
    
let decl_to_string: F.AST.decl -> string =
  FStar_Parser_ToDocument.decl_to_document >> doc_to_string
    
(* let item_to_string: F.AST.item -> string = *)
(*   FStar_Parser_ToDocument.decl_to_document >> doc_to_string *)

(* todo eliminate me *)
let last_of_global_ident (g: global_ident) =
  match g with
  | `Concrete {path; crate = _} -> Non_empty_list.last path
  | _ -> failwith "last_of_global_ident"
       
let rec pgeneric_param (p : generic_param)
  = match p with
  | Lifetime {ident} -> failwith "pgeneric_param:LIFETIME"
  | Type {ident; default = None} ->
    let v = F.pat @@ F.AST.PatVar (plocal_ident {ident with name = pgeneric_param_name ident.name}, None, []) in
    let t = F.term @@ F.AST.Name (F.lid ["Type"]) in
    F.pat @@ F.AST.PatAscribed (v, (t, None))
  | Type {ident; default = _} -> failwith "pgeneric_param:Type with default"
  | Const {ident; typ} -> failwith "todo"

let rec pgeneric_constraint (c: generic_constraint)
  = match c with
  | Lifetime _ -> failwith "pgeneric_constraint lifetime"
  | Type {typ; implements} ->
    let implements: trait_ref = implements in
    let trait = F.term @@ F.AST.Name (pglobal_ident implements.trait) in
    let args = List.map ~f:pgeneric_value implements.args in
    let tc = F.mk_e_app trait ((*pty typ::*)args) in
    F.pat @@ F.AST.PatAscribed (F.wild, (tc, None))

let rec pitem (e : item) =
  match e.v with
  | Fn { name; generics; body; params } ->  
      let pat = F.pat @@ F.AST.PatVar (
        F.id @@ last_of_global_ident name,
        None,
        []
      ) in
      let pat = F.pat @@ F.AST.PatApp (
             pat,
               List.map ~f:pgeneric_param generics.params
               @ List.map ~f:pgeneric_constraint generics.constraints
               @ List.map ~f:(fun {pat; typ_span; typ} ->
                     F.pat @@ F.AST.PatAscribed (
                       ppat pat,
                       (pty typ, None)
                     )
                   ) params
             ) in
      let pat = F.pat @@ F.AST.PatAscribed (
          pat,
          (pty body.typ, None)
        ) in
      F.decl @@ F.AST.TopLevelLet (
        NoLetQualifier,
        [
          pat, pexpr body
        ]
      )
  | TyAlias { name; generics; ty } ->
    let pat = F.pat @@ F.AST.PatVar (
        F.id @@ last_of_global_ident name,
        None,
        []
      ) in
    F.decl @@ F.AST.TopLevelLet (
      NoLetQualifier,
      [
        pat, pty ty
      ]
    )
  | Type { name; generics; variants } ->
    F.decl @@ F.AST.Tycon (
      false,
      false,
      [
        F.AST.TyconVariant (
          F.id @@ last_of_global_ident name,
          [],
          None,
          []
        )
      ]
    )
  | _ ->
      F.decl @@ F.AST.TopLevelLet (
        NoLetQualifier,
        [
          F.pat @@ F.AST.PatWild (None, []),
          F.unit
        ]
    )

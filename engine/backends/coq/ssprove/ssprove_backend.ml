open Hax_engine
open Utils
open Base
open Coq_ast

include
  Backend.Make
    (struct
      open Features
      include Off
      include On.Slice
      include On.Monadic_binding
      include On.Macro
      include On.Construct_base
      include On.Mutable_variable
      include On.Loop
      include On.For_loop
      include On.For_index_loop
      include On.State_passing_loop
    end)
    (struct
      let backend = Diagnostics.Backend.SSProve
    end)

module SubtypeToInputLanguage
    (FA : Features.T
            with type mutable_reference = Features.Off.mutable_reference
             and type continue = Features.Off.continue
             and type break = Features.Off.break
             and type mutable_pointer = Features.Off.mutable_pointer
             and type mutable_variable = Features.On.mutable_variable
             and type reference = Features.Off.reference
             and type raw_pointer = Features.Off.raw_pointer
             and type early_exit = Features.Off.early_exit
             and type question_mark = Features.Off.question_mark
             and type as_pattern = Features.Off.as_pattern
             and type lifetime = Features.Off.lifetime
             and type monadic_action = Features.Off.monadic_action
             and type arbitrary_lhs = Features.Off.arbitrary_lhs
             and type nontrivial_lhs = Features.Off.nontrivial_lhs
            (* and type loop = Features.Off.loop *)
             and type block = Features.Off.block
    (* and type for_loop = Features.Off.for_loop *)
    (* and type for_index_loop = Features.Off.for_index_loop *)
    (* and type state_passing_loop = Features.Off.state_passing_loo *)) =
struct
  module FB = InputLanguage

  include
    Subtype.Make (FA) (FB)
      (struct
        module A = FA
        module B = FB
        include Features.SUBTYPE.Id
        include Features.SUBTYPE.On.Monadic_binding
        include Features.SUBTYPE.On.Construct_base
        include Features.SUBTYPE.On.Slice
        include Features.SUBTYPE.On.Macro
        include Features.SUBTYPE.On.Loop
        include Features.SUBTYPE.On.For_loop
        include Features.SUBTYPE.On.For_index_loop
        include Features.SUBTYPE.On.State_passing_loop
      end)

  let metadata = Phase_utils.Metadata.make (Reject (NotInBackendLang backend))
end

module AST = Ast.Make (InputLanguage)
module BackendOptions = Backend.UnitBackendOptions
open Ast
module CoqNamePolicy = Concrete_ident.DefaultNamePolicy
module U = Ast_utils.MakeWithNamePolicy (InputLanguage) (CoqNamePolicy)
open AST

module SSProveLibrary : Library = struct
  module Notation = struct
    let additional_identifier : string = "b"

    let int_repr (x : string) (i : string) : string =
      i (* "i" ^ x ^ "(" ^ i ^ ")" *)

    let let_stmt (var : string) (expr : string) (typ : string) (body : string)
        (depth : int) : string =
      "letb" ^ " " ^ var ^ " " ^ ":=" ^ " " ^ expr ^ " "
      (* ^ " (" ^ expr ^ ") "  *)
      ^ ":of:"
      ^ " " ^ typ
      (* ^ ":" ^ " " *)
      (* ^ "both _ _" ^ " " ^ "(" ^ typ ^ ")" *)
      ^ " "
      ^ "in" ^ newline_indent depth ^ body

    let let_mut_stmt (var : string) (expr : string) (typ : string)
        (body : string) (depth : int) : string =
      "letbm" ^ " " ^ var ^ " " ^ "loc(" ^ var ^ "_loc" ^ ")" ^ " " ^ ":="
      (* ^ " (" ^ expr ^ ") " ^ ":" ^ " " ^ "both _ _" ^ " " ^ "(" ^ typ ^ ")" *)
      ^ " "
      ^ expr ^ " " ^ ":of:" ^ " " ^ typ ^ " " ^ "in" ^ newline_indent depth
      ^ body

    let let_bind_stmt (var : string) (expr : string) (typ : string)
        (body : string) (depth : int) : string =
      "let_bind_b" ^ " " ^ var ^ " " ^ ":=" ^ " " ^ expr ^ " "
      (* ^ " (" ^ expr ^ ") "  *)
      ^ ":of:"
      ^ " " ^ typ
      (* ^ ":" ^ " " *)
      (* ^ "both _ _" ^ " " ^ "(" ^ typ ^ ")" *)
      ^ " "
      ^ "in" ^ newline_indent depth ^ body

    let let_bind_mut_stmt (var : string) (expr : string) (typ : string)
        (body : string) (depth : int) : string =
      "let_bind_bm" ^ " " ^ var ^ " " ^ "loc(" ^ var ^ "_loc" ^ ")" ^ " " ^ ":="
      (* ^ " (" ^ expr ^ ") " ^ ":" ^ " " ^ "both _ _" ^ " " ^ "(" ^ typ ^ ")" *)
      ^ " "
      ^ expr ^ " " ^ ":of:" ^ " " ^ typ ^ " " ^ "in" ^ newline_indent depth
      ^ body

    let type_str : string = "choice_type"
    let bool_str : string = "'bool"
    let unit_str : string = "'unit"

    let if_stmt (cond : string) (then_e : string) (else_e : string)
        (depth : int) : string =
      "ifb" ^ " " ^ cond ^ newline_indent depth ^ "then" ^ " " ^ then_e
      ^ newline_indent depth ^ "else" ^ " " ^ else_e

    let match_stmt (expr : string) (arms : (string * string) list) (depth : int)
        : string =
      "matchb" ^ " " ^ expr ^ " " ^ "with" ^ newline_indent depth
      ^ List.fold_left ~init:""
          ~f:(fun y (x_match, x_body) ->
            y ^ "|" ^ " " ^ x_match ^ " " ^ "=>"
            ^ newline_indent (depth + 1)
            ^ x_body ^ newline_indent depth)
          arms
      ^ "end"
  end
end

module SSP = Coq (SSProveLibrary)
open Analysis_utils
open Analyses

module StaticAnalysis (* : ANALYSIS *) = struct
  module A = InputLanguage

  module FunctionDependency (* : ANALYSIS *) =
  [%functor_application
  Analyses.Function_dependency InputLanguage]

  module MutableVariables (* : ANALYSIS *) =
  [%functor_application
  Analyses.Mutable_variables InputLanguage]

  type pre_data = FunctionDependency.pre_data

  type analysis_data = {
    func_dep : FunctionDependency.analysis_data;
    mut_var : MutableVariables.analysis_data;
  }

  let analyse (pre_data : FunctionDependency.pre_data) items =
    let func_dep = FunctionDependency.analyse pre_data items in
    let mut_var =
      MutableVariables.analyse (func_dep : MutableVariables.pre_data) items
    in
    { func_dep; mut_var }
end

module Context = struct
  type t = {
    current_namespace : string * string list;
    analysis_data : StaticAnalysis.analysis_data;
  }
end

let primitive_to_string (id : primitive_ident) : string =
  match id with
  | Deref -> "(TODO: Deref)" (* failwith "Deref" *)
  | Cast -> "cast_int (WS2 := _)" (* failwith "Cast" *)
  | LogicalOp op -> ( match op with And -> "andb" | Or -> "orb")

open Phase_utils

module TransformToInputLanguage (* : PHASE *) =
  [%functor_application
    Phases.Reject.RawOrMutPointer(Features.Rust)
    |> Phases.And_mut_defsite
    |> Phases.Reconstruct_for_loops
    |> Phases.Direct_and_mut
    |> Phases.Reject.Arbitrary_lhs
    |> Phases.Drop_blocks
    (* |> Phases.Reject.Continue *)
    |> Phases.Drop_references
    |> Phases.Trivialize_assign_lhs
    |> Phases.Reconstruct_question_marks
    |> Side_effect_utils.Hoist
    (* |> Phases.Local_mutation *)
    |> Phases.State_passing_loop
    |> Phases.Reject.Continue
    |> Phases.Cf_into_monads
    |> Phases.Reject.EarlyExit
    (* |> Phases.Functionalize_loops *)
    |> Phases.Reject.As_pattern
    |> SubtypeToInputLanguage
    |> Identity
  ]
  [@ocamlformat "disable"]
let token_list (tokens : string) : string list list =
  List.map ~f:(split_str ~on:"=") (split_str ~on:"," tokens)

let get_argument (s : string) (token_list : string list list) =
  List.find_map
    ~f:(function
      | [ v; a ] when String.equal (String.strip v) s -> Some a | _ -> None)
    token_list

let wrap_type_in_both (l : string) (i : string) (a : SSP.AST.ty) =
  SSP.AST.AppTy (SSP.AST.NameTy ("both" ^ " " ^ l ^ " " ^ i), [ a ])

let token_list (tokens : string) : string list list =
  List.map ~f:(split_str ~on:"=") (split_str ~on:"," tokens)

let get_argument (s : string) (token_list : string list list) =
  List.find_map
    ~f:(function
      | [ v; a ] when String.equal (String.strip v) s -> Some a | _ -> None)
    token_list

let strip (x : string) =
  String.strip
    ?drop:(Some (function '\"' -> true | _ -> false))
    (String.strip x)

let strip_or_error (err : string) (s : string option) span =
  match s with
  | Some x -> strip x
  | None -> Error.unimplemented ~details:err span

let pconcrete_ident (id : concrete_ident) : string =
  U.Concrete_ident_view.to_definition_name id

let magic_id_raw_local_ident = LocalIdent.mk_id Expr (-765142)

let plocal_ident (e : LocalIdent.t) =
  U.Concrete_ident_view.local_name
    (match String.chop_prefix ~prefix:"impl " e.name with
     | Some name -> "impl_" ^ Int.to_string ([%hash: string] name)
     | _ -> e.name)

let wrap_type_in_both (l : string) (i : string) (a : SSP.AST.ty) =
  SSP.AST.AppTy (SSP.AST.NameTy ("both" ^ " " ^ l ^ " " ^ i), [ a ])

module Make (Ctx : sig
  val ctx : Context.t
end) =
struct
  open Ctx
  (* let id = U.Concrete_ident_view.to_view id in *)
  (* String.concat ~sep:"_" (id.path @ [id.definition]) *)

  let pglobal_ident (id : global_ident) : string =
    match id with
    | `Projector (`Concrete cid) | `Concrete cid -> pconcrete_ident cid
    | `Primitive p_id -> primitive_to_string p_id
    | `TupleType i -> "TODO (global ident) tuple type"
    | `TupleCons i -> "TODO (global ident) tuple cons"
    | `Projector (`TupleField (i, j)) | `TupleField (i, j) ->
        "TODO (global ident) tuple field"
    | _ -> .

  module TODOs_debug = struct
    let __TODO_pat__ _ s = SSP.AST.Ident (s ^ " todo(pat)")
    let __TODO_ty__ _ s : SSP.AST.ty = SSP.AST.NameTy (s ^ " todo(ty)")
    let __TODO_item__ _ s = SSP.AST.Unimplemented (s ^ " todo(item)")

    let __TODO_term__ _ s =
      SSP.AST.Const (SSP.AST.Const_string (s ^ " todo(term)"))
  end

  module TODOs = struct
    let __TODO_ty__ span s : SSP.AST.ty =
      Error.unimplemented ~details:("[ty] node " ^ s) span

    let __TODO_pat__ span s =
      Error.unimplemented ~details:("[pat] node " ^ s) span

    let __TODO_term__ span s =
      Error.unimplemented ~details:("[expr] node " ^ s) span

    let __TODO_item__ span s = SSP.AST.Unimplemented (s ^ " todo(item)")
  end

  open TODOs

  let pint_kind (k : int_kind) : SSP.AST.int_type =
    {
      size =
        (match k.size with
        | S8 -> U8
        | S16 -> U16
        | S32 -> U32
        | S64 -> U64
        | S128 -> U128
        | SSize -> USize);
      signed = k.signedness == Signed;
    }

  let rec pliteral (e : literal) =
    match e with
    | String s -> SSP.AST.Const_string s
    | Char c -> SSP.AST.Const_char (Char.to_int c)
    | Int { value; kind } -> SSP.AST.Const_int (value, pint_kind kind)
    | Float _ -> failwith "Float: todo"
    | Bool b -> SSP.AST.Const_bool b

  let operators =
    let c = Global_ident.of_name Value in
    [
      (c Rust_primitives__hax__array_of_list, (3, [ ""; ".a["; "]<-"; "" ]));
      (c Core__ops__index__Index__index, (2, [ ""; ".a["; "]" ]));
      (c Core__ops__bit__BitXor__bitxor, (2, [ ""; " .^ "; "" ]));
      (c Core__ops__bit__BitAnd__bitand, (2, [ ""; " .& "; "" ]));
      (c Core__ops__bit__BitOr__bitor, (2, [ ""; " .| "; "" ]));
      (c Core__ops__arith__Add__add, (2, [ ""; " .+ "; "" ]));
      (c Core__ops__arith__Sub__sub, (2, [ ""; " .- "; "" ]));
      (c Core__ops__arith__Mul__mul, (2, [ ""; " .* "; "" ]));
      (c Core__ops__arith__Div__div, (2, [ ""; " ./ "; "" ]));
      (c Core__cmp__PartialEq__eq, (2, [ ""; " =.? "; "" ]));
      (c Core__cmp__PartialOrd__lt, (2, [ ""; " <.? "; "" ]));
      (c Core__cmp__PartialOrd__le, (2, [ ""; " <=.? "; "" ]));
      (c Core__cmp__PartialOrd__ge, (2, [ ""; " >=.? "; "" ]));
      (c Core__cmp__PartialOrd__gt, (2, [ ""; " >.? "; "" ]));
      (c Core__cmp__PartialEq__ne, (2, [ ""; " <> "; "" ]));
      (c Core__ops__arith__Rem__rem, (2, [ ""; " .% "; "" ]));
      (c Core__ops__bit__Shl__shl, (2, [ ""; " shift_left "; "" ]));
      (c Core__ops__bit__Shr__shr, (2, [ ""; " shift_right "; "" ]));
      (* TODO: those two are not notations/operators at all, right? *)
      (* (c "secret_integers::rotate_left", (2, [ "rol "; " "; "" ])); *)
      (* (c "hacspec::lib::foldi", (4, [ "foldi "; " "; " "; " "; "" ])); *)
      (* (c "secret_integers::u8", (0, ["U8"])); *)
      (* (c "secret_integers::u16", (0, ["U16"])); *)
      (* (c "secret_integers::u32", (0, ["U32"])); *)
      (* (c "secret_integers::u64", (0, ["U64"])); *)
      (* (c "secret_integers::u128", (0, ["U128"])); *)
    ]
    (* [ *)
    (*   ( c "std::core::array::update_array_at", *)
    (*     (3, [ "nseq_array_or_seq "; ".["; "]<-"; "" ]) ); *)
    (*   ( c "core::ops::index::Index::index", *)
    (*     (2, [ "nseq_array_or_seq "; ".["; "]" ]) ); *)
    (*   (c "core::ops::bit::BitXor::bitxor", (2, [ ""; ".^"; "" ])); *)
    (*   (c "core::ops::bit::BitAnd::bitand", (2, [ ""; ".&"; "" ])); *)
    (*   (c "core::ops::bit::BitOr::bitor", (2, [ ""; ".|"; "" ])); *)
    (*   (c "core::ops::arith::Add::add", (2, [ ""; ".+"; "" ])); *)
    (*   (c "core::ops::arith::Sub::sub", (2, [ ""; ".-"; "" ])); *)
    (*   (c "core::ops::arith::Mul::mul", (2, [ ""; ".*"; "" ])); *)
    (*   (`Primitive (BinOp Add), (2, [ ""; ".+"; "" ])); *)
    (*   (`Primitive (BinOp Sub), (2, [ ""; ".-"; "" ])); *)
    (*   (`Primitive (BinOp Mul), (2, [ ""; ".*"; "" ])); *)
    (*   (`Primitive (BinOp Div), (2, [ ""; "./"; "" ])); *)
    (*   (`Primitive (BinOp Eq), (2, [ ""; "=.?"; "" ])); *)
    (*   (`Primitive (BinOp Lt), (2, [ ""; "<.?"; "" ])); *)
    (*   (`Primitive (BinOp Le), (2, [ ""; "<=.?"; "" ])); *)
    (*   (`Primitive (BinOp Ge), (2, [ ""; ">=.?"; "" ])); *)
    (*   (`Primitive (BinOp Gt), (2, [ ""; ">.?"; "" ])); *)
    (*   (`Primitive (BinOp Ne), (2, [ ""; "<>"; "" ])); *)
    (*   (`Primitive (BinOp Rem), (2, [ ""; ".%"; "" ])); *)
    (*   (`Primitive (BinOp BitXor), (2, [ ""; ".^"; "" ])); *)
    (*   (`Primitive (BinOp BitAnd), (2, [ ""; ".&"; "" ])); *)
    (*   (`Primitive (BinOp BitOr), (2, [ ""; ".|"; "" ])); *)
    (*   (`Primitive (BinOp Shl), (2, [ ""; " shift_left "; "" ])); *)
    (*   (`Primitive (BinOp Shr), (2, [ ""; " shift_right "; "" ])); *)
    (*   (c "secret_integers::rotate_left", (2, [ "rol "; " "; "" ])); *)
    (*   (c "hacspec::lib::foldi", (4, [ "foldi_both' "; " "; " (ssp"; ") "; "" ])); *)
    (*   ( c "hacspec::lib::fold", *)
    (*     (4, [ "foldi_both' "; " "; " (fun {L I} => (ssp"; ")) "; "" ]) ); *)
    (*   ( c "hacspec_lib_tc::fold", *)
    (*     (4, [ "foldi_both' "; " "; " (fun {L I} => (ssp"; ")) "; "" ]) ); *)
    (*   ( c "hacspec_lib_tc::foldi", *)
    (*     (4, [ "foldi_both' "; " "; " (fun {L I} {_ _} => (ssp"; ")) "; "" ]) ); *)
    (*   (\* (c "secret_integers::u8", (0, ["U8"])); *\) *)
    (*   (\* (c "secret_integers::u16", (0, ["U16"])); *\) *)
    (*   (\* (c "secret_integers::u32", (0, ["U32"])); *\) *)
    (*   (\* (c "secret_integers::u64", (0, ["U64"])); *\) *)
    (*   (\* (c "secret_integers::u128", (0, ["U128"])); *\) *)
    (* ] *)
    |> Map.of_alist_exn (module Global_ident)

  let index_of_field = function
    | `Concrete cid -> (
        try Some (Int.of_string @@ pconcrete_ident cid) with _ -> None)
    | `TupleField (nth, _) -> Some nth
    | _ -> None

  (* let is_field_an_index = index_of_field >> Option.is_some *)

  module LocalIdentOrLisIis = StaticAnalysis.MutableVariables.LocalIdentOrData(struct type ty = string list * string list [@@deriving compare, sexp] end)

  let rec pty span (t : ty) : SSP.AST.ty =
    match t with
    | TBool -> SSP.AST.Bool
    | TChar -> __TODO_ty__ span "char"
    | TInt k -> SSP.AST.Int (pint_kind k)
    | TStr -> SSP.AST.NameTy "chString"
    (* TODO: chString ??? *)
    (* __TODO_ty__ span "str" *)
    (* | TFalse -> __TODO_ty__ span "false" *)
    | TApp { ident = `TupleType 0 as ident; args = [] } -> SSP.AST.Unit
    | TApp { ident = `TupleType 1; args = [ GType ty ] } -> pty span ty
    | TApp { ident = `TupleType n; args } when n >= 2 ->
        SSP.AST.Product (args_ty span args)
    | TApp { ident; args } ->
        SSP.AST.AppTy (SSP.AST.NameTy (pglobal_ident ident), args_ty span args)
    | TArrow (inputs, output) ->
        List.fold_right ~init:(pty span output)
          ~f:(fun x y -> SSP.AST.Arrow (x, y))
          (List.map ~f:(pty span) inputs)
    | TFloat _ -> __TODO_ty__ span "pty: Float"
    | TArray { typ; length = { e = Literal (Int { value; _ }) } } ->
        SSP.AST.ArrayTy (pty span typ, value)
    | TArray { typ; length } ->
        SSP.AST.ArrayTy
          ( pty span typ,
            "(" ^ "is_pure" ^ " " ^ "("
            ^ SSP.term_to_string_with_paren (pexpr (Map.empty (module LocalIdent)) false length) 0
            ^ ")" ^ ")" )
        (* TODO: check int.to_string is correct! *)
    | TSlice { ty; _ } -> SSP.AST.SliceTy (pty span ty)
    | TParam i -> SSP.AST.NameTy (plocal_ident i)
    | TAssociatedType {impl; item} -> SSP.AST.NameTy (pconcrete_ident item)
    | TOpaque _ -> __TODO_ty__ span "pty: TAssociatedType/TOpaque"
    | _ -> .

  and args_ty span (args : generic_value list) : SSP.AST.ty list =
    (* List.map ~f:pty *)
    match args with
    | arg :: xs ->
        (match arg with
        | GLifetime { lt; witness } -> __TODO_ty__ span "lifetime"
        | GType typ -> pty span typ
        | GConst { typ; _ } ->
            wrap_type_in_both "(fset [])" "(fset [])" (pty span typ))
        :: args_ty span xs
    | [] -> []

  and ppat (p : pat) : SSP.AST.pat =
    match p.p with
    | PWild -> SSP.AST.WildPat
    | PAscription { typ; pat } ->
        SSP.AST.AscriptionPat (ppat pat, pty p.span typ)
    | PBinding
        {
          mut = Immutable;
          mode = _;
          subpat (* = None *);
          var;
          typ = _ (* we skip type annot here *);
        } ->
        SSP.AST.Ident (plocal_ident var)
    | PBinding
        {
          mut = Mutable _;
          mode = _;
          subpat;
          (* TODO no subpat? *)
          var;
          typ = _ (* we skip type annot here *);
        } ->
        SSP.AST.Ident (plocal_ident var) (* TODO Mutable binding ! *)
    | PArray { args } -> __TODO_pat__ p.span "Parray?"
    | PConstruct { name = `TupleCons 0; args = [] } -> SSP.AST.WildPat (* UnitPat *)
    | PConstruct { name = `TupleCons 1; args = [ { pat } ] } ->
        __TODO_pat__ p.span "tuple 1"
    | PConstruct { name = `TupleCons n; args } ->
        SSP.AST.TuplePat (List.map ~f:(fun { pat } -> ppat pat) args)
    | PConstruct { name; args; is_record = true } ->
        SSP.AST.RecordPat (pglobal_ident name, List.map ~f:(fun {field; pat} -> (pglobal_ident field, ppat pat)) args)
    | PConstruct { name; args; is_record = false } ->
        SSP.AST.ConstructorPat
          (pglobal_ident name, List.map ~f:(fun p -> ppat p.pat) args)
    | PConstant { lit } -> SSP.AST.Lit (pliteral lit)
    | _ -> .

  (* and analyse_fset (data : StaticAnalysis.MutableVariables.analysis_data) items = *)
  (*   (object *)
  (*      inherit [_] expr_reduce as super *)
  (*      inherit [_] U.Reducers.expr_list_monoid as m (\* TODO: Raname into list monoid *\) *)
  (*      method visit_t _ _ = m#zero *)
  (*      (\* method visit_mutability (_f : string -> _ -> _) (ctx : string) _ = m#zero *\) *)
  (*      method visit_mutability (f : string -> _ -> _) (ctx : string) mu = *)
  (*        match mu with Mutable wit -> f ctx wit | _ -> m#zero *)

  (*      method! visit_PBinding env mut _ var _typ subpat = *)
  (*        m#plus *)
  (*          (match mut with *)
  (*           | Mutable _ -> *)
  (*             var.name *)
  (*           | Immutable -> *)
  (*             (\* Set.singleton (module U.TypedLocalIdent) (var, typ) *\) *)
  (*             "") *)
  (*          (Option.value_map subpat ~default:m#zero *)
  (*             ~f:(fst >> super#visit_pat env)) *)

  (*      method! visit_global_ident (env : string) (x : Global_ident.t) = *)
  (*        match x with *)
  (*        | `Projector (`Concrete cid) | `Concrete cid -> *)
  (*          (match Map.find data (Uprint.Concrete_ident_view.to_definition_name cid) with *)
  (*           | Some (x,_) -> Set.of_list (module LocalIdent) x *)
  (*           | _ -> m#zero) *)
  (*        | _ -> m#zero *)

  (*      method visit_expr (env : string) e = [(e, env)] (\* :: super#visit_expr f e *\) *)
  (*   end) *)
  (*   #visit_expr *)
  (*     "" *)

  and pexpr (env : (LocalIdentOrLisIis.W.t list) Map.M(LocalIdent).t) (add_solve : bool) (e : expr) : SSP.AST.term =
    let span = e.span in
    (match (add_solve, e.e) with
    | ( true,
        ( Construct { is_record = true; _ }
        | If _ | Match _ | Literal _
        | Construct { constructor = `TupleCons _; _ }
        | App _ | GlobalVar _ | LocalVar _ ) ) ->
        fun x -> SSP.AST.App (SSP.AST.Var "solve_lift", [ x ])
    | _ -> fun x -> x)
      (match e.e with
      | Literal lit ->
          SSP.AST.App
            ( SSP.AST.Var "ret_both",
              [
                SSP.AST.TypedTerm (SSP.AST.Const (pliteral lit), pty span e.typ);
              ] )
      | LocalVar local_ident -> SSP.AST.NameTerm (plocal_ident local_ident)
      | GlobalVar (`TupleCons 0)
      | Construct { constructor = `TupleCons 0; fields = [] } ->
          SSP.AST.App (SSP.AST.Var "ret_both", [ SSP.AST.UnitTerm ])
      | GlobalVar global_ident -> SSP.AST.Var (pglobal_ident global_ident)
      | App
          {
            f = { e = GlobalVar (`Projector (`TupleField (n, len))) };
            args = [ arg ];
          } ->
          __TODO_term__ span "app global vcar projector tuple"
      | App { f = { e = GlobalVar x }; args } when Map.mem operators x ->
          let arity, op = Map.find_exn operators x in
          if List.length args <> arity then failwith "Bad arity";
          let args =
            List.map ~f:(fun x -> SSP.AST.Value ((pexpr env false) x, true)) args
          in
          SSP.AST.AppFormat (op, args)
      (* | App { f = { e = GlobalVar x }; args } -> *)
      (*    __TODO_term__ span "GLOBAL APP?" *)
      | App { f; args } ->
          let base = (pexpr env false) f in
          let args = List.map ~f:(pexpr env false) args in
          SSP.AST.App (base, args)
      | If { cond; then_; else_ } ->
          SSP.AST.If
            ( (pexpr env false) cond,
              (pexpr env false) then_,
              Option.value_map else_ ~default:(SSP.AST.Literal "()")
                ~f:(pexpr env false) )
      | Array l -> SSP.AST.Array (List.map ~f:(pexpr env add_solve) l)
      | Let { lhs; rhs; body; monadic } ->
        let extra_set, extra_env = LocalIdentOrLisIis.analyse_expr ctx.analysis_data.mut_var env rhs in
        let new_env =
          extend_env
            env
            (Map.of_alist_exn (module LocalIdent)
               (List.map
                  ~f:(fun v -> (v, extra_set))
                  (Set.to_list (U.Reducers.variables_of_pat lhs))))
        in
        (
          match monadic with
          | Some (MException typ, _) ->
              SSP.AST.AppFormat
                ( [
                    "letm[choice_typeMonad.result_bind_code (";
                    (*typ*)
                    ")] ";
                    (*p*)
                    " := ";
                    (*expr*)
                    " in";
                    "";
                    (*body*)
                    "";
                  ],
                  [
                    SSP.AST.Typing (pty span typ);
                    SSP.AST.Variable (ppat lhs);
                    SSP.AST.Value ((pexpr env false) rhs, false);
                    SSP.AST.Newline 0;
                    SSP.AST.Value ((pexpr new_env add_solve) body, false);
                  ] )
          | Some (MResult typ, _) ->
              SSP.AST.AppFormat
                ( [
                    "letm[choice_typeMonad.result_bind_code (";
                    (*typ*)
                    ")] ";
                    (*p*)
                    " := ";
                    (*expr*)
                    " in";
                    "";
                    (*body*)
                    "";
                  ],
                  [
                    SSP.AST.Typing (pty span typ);
                    SSP.AST.Variable (ppat lhs);
                    SSP.AST.Value ((pexpr env false) rhs, false);
                    SSP.AST.Newline 0;
                    SSP.AST.Value ((pexpr new_env add_solve) body, false);
                  ] )
          | Some (MOption, _) ->
              SSP.AST.AppFormat
                ( [
                    "letm[choice_typeMonad.option_bind_code] ";
                    (*p*)
                    " := ";
                    (*expr*)
                    " in";
                    "";
                    (*body*)
                    "";
                  ],
                  [
                    SSP.AST.Variable (ppat lhs);
                    SSP.AST.Value ((pexpr env false) rhs, false);
                    SSP.AST.Newline 0;
                    SSP.AST.Value ((pexpr new_env add_solve) body, false);
                  ] )
          | None ->
              if is_mutable_pat lhs then
                SSP.AST.AppFormat
                  ( [
                      "letb ";
                      (*p*)
                      " loc(" (*p_loc*);
                      ") := ";
                      (*expr*)
                      " in";
                      "";
                      (*body*)
                      "";
                    ],
                    [
                      SSP.AST.Variable (ppat lhs);
                      SSP.AST.Variable
                        (match (List.map ~f:(fun x -> SSP.AST.Ident (x.name ^ "_loc")) (Set.to_list (U.Reducers.variables_of_pat lhs))) with
                         | [] -> SSP.AST.WildPat
                         | [x] -> x
                         | xs -> SSP.AST.TuplePat xs
                        );
                      SSP.AST.Value ((pexpr env false) rhs, false);
                      SSP.AST.Newline 0;
                      SSP.AST.Value ((pexpr (let new_env =
                                               extend_env
                                                 new_env
                                                 (Map.of_alist_exn (module LocalIdent)
                                                    (List.map
                                                       ~f:(fun v -> (v, [LocalIdentOrLisIis.W.Identifier v]))
                                                       (Set.to_list (U.Reducers.variables_of_pat lhs))))
                                             in
                                             new_env) add_solve) body, false);
                    ] )
              else
                SSP.AST.AppFormat
                  ( [ "letb "; (*p*) " := "; (*expr*) " in"; ""; (*body*) "" ],
                    [
                      SSP.AST.Variable (ppat lhs);
                      SSP.AST.Value ((pexpr env false) rhs, false);
                      SSP.AST.Newline 0;
                      SSP.AST.Value ((pexpr new_env add_solve) body, false);
                    ] )
                (* SSP.AST.Let *)
                (*   { *)
                (*     pattern = ppat lhs; *)
                (*     mut = is_mutable_pat lhs; *)
                (*     value = (pexpr env false) rhs; *)
                (*     body = (pexpr env add_solve) body; *)
                (*     value_typ = pty lhs.span lhs.typ; *)
                (*     monad_typ = Option.map ~f:(fun (m, _) -> match m with *)
                (*         | MException (typ) -> SSP.AST.Exception (pty span typ) *)
                (*         | MResult (typ) -> SSP.AST.Result (pty span typ) *)
                (*         | MOption -> SSP.AST.Option) monadic; *)
                (*   } *))
      | EffectAction _ -> . (* __TODO_term__ span "monadic action" *)
      | Match { scrutinee; arms } ->
          SSP.AST.Match
            ( (pexpr env false) scrutinee,
              List.map
                ~f:(fun { arm = { arm_pat; body } } ->
                  (ppat arm_pat, (pexpr env false) body))
                arms )
      | Ascription { e; typ } -> __TODO_term__ span "asciption"
      | Construct { constructor = `TupleCons 1; fields = [ (_, e) ]; base } ->
          (pexpr env false) e
      | Construct { constructor = `TupleCons n; fields; base } ->
          SSP.AST.App
            ( SSP.AST.Var "prod_b",
              [ SSP.AST.Tuple (List.map ~f:(snd >> pexpr env false) fields) ] )
      | Construct { is_record = true; constructor; fields; base = None } ->
          SSP.AST.RecordConstructor
            ( "t_" ^ pglobal_ident constructor,
              List.map
                ~f:(fun (f, e) -> (pglobal_ident f, (pexpr env false) e))
                fields )
      | Construct { is_record = true; constructor; fields; base = Some (x, _) }
        ->
          SSP.AST.RecordUpdate
            ( pglobal_ident constructor,
              (pexpr env false) x,
              List.map
                ~f:(fun (f, e) -> (pglobal_ident f, (pexpr env false) e))
                fields )
          (* TODO: Is there only 1 field? *)
      | Construct { constructor; fields = [ (f, e) ]; base } ->
          SSP.AST.App
            (SSP.AST.Var (pglobal_ident constructor), [ (pexpr env add_solve) e ])
      | Construct { constructor; fields; base } ->
          (* __TODO_term__ span "constructor" *)
          SSP.AST.App
            ( SSP.AST.Var (pglobal_ident constructor),
              List.map ~f:(snd >> pexpr env add_solve) fields )
      | Closure { params; body } ->
          SSP.AST.Lambda (List.map ~f:ppat params, (pexpr (extend_env_with_params env params) add_solve) body)
      | MacroInvokation { macro; args; witness } ->
          Error.raise
          @@ {
               kind = UnsupportedMacro { id = [%show: global_ident] macro };
               span = e.span;
             }
      | Assign { e } ->
          SSP.AST.Const (SSP.AST.Const_string ("assign" ^ " todo(term)"))
          (* __TODO_term__ span "assign" *)
      | Loop { body; kind; state = None; label; witness } ->
          (pexpr env false)
            {
              e =
                Loop
                  {
                    body;
                    kind;
                    state =
                      Some
                        {
                          init =
                            {
                              e =
                                Construct
                                  {
                                    is_record = false;
                                    is_struct = false;
                                    base = None;
                                    constructor = `TupleCons 0;
                                    fields = [];
                                  };
                              span = Span.dummy ();
                              typ = TApp { ident = `TupleType 0; args = [] };
                            };
                          bpat =
                            {
                              p =
                                PConstruct
                                  {
                                    name = `TupleCons 0;
                                    args = [];
                                    is_record = false;
                                    is_struct = false;
                                  };
                              span = Span.dummy ();
                              typ = TApp { ident = `TupleType 0; args = [] };
                            };
                          witness =
                            Features.On.state_passing_loop
                            (* state_passing_loop *);
                        };
                    label;
                    witness;
                  };
              typ = e.typ;
              span = e.span;
            }
      | Loop
          {
            body;
            kind = ForIndexLoop { start; end_; var; var_typ; _ };
            state = Some { init; bpat; _ };
            label;
            _;
          } ->
          SSP.AST.App
            ( SSP.AST.Var "foldi_both",
              [
                (pexpr env false) start;
                (pexpr env false) end_;
                SSP.AST.Lambda
                  ( [ (* SSP.AST.Ident "{L I _ _}";  *) SSP.AST.Ident (plocal_ident var) ],
                    SSP.AST.App
                      ( SSP.AST.Var "ssp",
                        [ SSP.AST.Lambda (
                              [ ppat bpat ],
                              both_type_expr
                                (extend_env env (Map.of_alist_exn (module LocalIdent) ([
                                     (var, [LocalIdentOrLisIis.W.Data ([(plocal_ident var) ^ "?"], [(plocal_ident var) ^ "?"])])
                                   ] @
                                     (List.map
                                        ~f:(fun v -> (v, [LocalIdentOrLisIis.W.Data ([(plocal_ident v) ^ "!"], [(plocal_ident v) ^ "!"])]))
                                        (vars_from_pat bpat)))
                                   )) true [] body) ] )
                  );
                (pexpr env false) init;
              ] )
      | Loop
          {
            body;
            kind = ForLoop { pat; it; _ };
            state = Some { init; bpat; _ };
            label;
            _;
          } ->
        let extra_set_init, extra_env = LocalIdentOrLisIis.analyse_expr ctx.analysis_data.mut_var env init in
        let new_env =
          extend_env
            env
            (Map.of_alist_exn (module LocalIdent)
               (List.map
                  ~f:(fun v -> (v, extra_set_init))
                  (Set.to_list (U.Reducers.variables_of_pat bpat))))
        in
        let extra_set_iter, extra_env = LocalIdentOrLisIis.analyse_expr ctx.analysis_data.mut_var env it in
        let new_env =
          extend_env
            new_env
            (Map.of_alist_exn (module LocalIdent)
               (List.map
                  ~f:(fun v -> (v, extra_set_iter))
                  (Set.to_list (U.Reducers.variables_of_pat bpat))))
        in
          SSP.AST.App
            ( SSP.AST.Var "foldi_both_list",
              [
                (pexpr env false) it;
                SSP.AST.Lambda
                  ( [ (* SSP.AST.Ident "{L I _ _}";  *) ppat pat ],
                    SSP.AST.App
                      ( SSP.AST.Var "ssp",
                        [ SSP.AST.Lambda ([ ppat bpat ], both_type_expr new_env true (extra_set_iter @ extra_set_init) body) ] )
                  );
                (pexpr env false) init;
              ] )
      | Loop { body; kind; state; label; _ } ->
          SSP.AST.Const (SSP.AST.Const_string ("other loop" ^ " todo(term)"))
      (* __TODO_term__ span "other loop" *)
      (* | Break { e; _ } -> *)
      (*     SSP.AST.Const (SSP.AST.Const_string ("break" ^ " todo(term)")) *)
      (*     (* __TODO_term__ span "break" *) *)
      | _ -> .)

  and vars_from_pat : pat -> LocalIdent.t list = U.Reducers.variables_of_pat >> Set.to_list

  and env_from_param (params : pat list) : (LocalIdentOrLisIis.W.t list) Map.M(LocalIdent).t =
    (Map.of_alist_exn (module LocalIdent)
       (List.concat_mapi ~f:(fun i pat -> (List.map ~f:(fun var ->
            (var, [LocalIdentOrLisIis.W.Data (["L" ^ Int.to_string (i + 1)],["I" ^ Int.to_string (i + 1)])])) (vars_from_pat pat))
          ) params))
  and extend_env (env : (LocalIdentOrLisIis.W.t list) Map.M(LocalIdent).t) (env_ext : (LocalIdentOrLisIis.W.t list) Map.M(LocalIdent).t) : (LocalIdentOrLisIis.W.t list) Map.M(LocalIdent).t =
    Map.merge_skewed
      env
      env_ext
      ~combine:(fun ~key a b -> a @ b) (* TODO: Just combine values? Should do this as sets! *)
  and extend_env_with_params (env : (LocalIdentOrLisIis.W.t list) Map.M(LocalIdent).t) (params : pat list) : (LocalIdentOrLisIis.W.t list) Map.M(LocalIdent).t =
    extend_env env (env_from_param params)

  and analyse_env_of_expr (env : (LocalIdentOrLisIis.W.t list) Map.M(LocalIdent).t) (e : expr) (extra_set) =
    let expr_env, new_env = LocalIdentOrLisIis.analyse_expr ctx.analysis_data.mut_var env e in
    let expr_env = expr_env @ extra_set in
    let identifiers = List.filter_map ~f:(function Identifier x -> Some x | Data _ -> None) expr_env in
    let data = List.filter_map ~f:(function Identifier _ -> None | Data x -> Some x) expr_env in
    let lis, iis = (List.concat *** List.concat) (List.unzip data) in
    identifiers, lis, iis, new_env


  and both_type_expr
      (env : (LocalIdentOrLisIis.W.t list) Map.M(LocalIdent).t)
      (add_solve : bool)
      (extra_set : LocalIdentOrLisIis.W.t list)
      (e : expr) =
    let identifiers, lis, iis, new_env = analyse_env_of_expr env e extra_set in
    let mvars_ext_fset_str = "fset"^" "^"["^String.concat ~sep:";" (List.map ~f:(fun x -> (plocal_ident x) ^ "_loc") identifiers) ^ "]"
    in
    let lis_str = String.concat ~sep:":|:" (lis @ [mvars_ext_fset_str]) in
    let iis_str = if List.length iis == 0 then "(fset [])" else String.concat ~sep:":|:" iis in
    SSP.AST.TypedTerm ((pexpr env add_solve) e, wrap_type_in_both ("(*"^Int.to_string (List.length identifiers)^"*)" ^ "(" ^ lis_str ^ ")") ("(" ^ iis_str ^ ")") (pty e.span e.typ))

  and is_mutable_pat (pat : pat) =
    match pat.p with
    | PWild -> false
    | PAscription { typ; typ_span; pat } -> is_mutable_pat pat
    | PConstruct { name = `TupleCons _; args } ->
        List.fold ~init:false ~f:( || )
          (List.map ~f:(fun p -> is_mutable_pat p.pat) args)
    | PConstruct { name; args; is_record; is_struct } -> false
    | PArray { args } ->
        (* List.fold ~init:false ~f:(||) (List.map ~f:(fun p -> is_mutable_pat p) args) *)
        false
    | PConstant { lit } -> false
    | PBinding { mut = Mutable _ } -> true
    | PBinding { mut; mode; var; typ; subpat = Some (spat, _) } ->
        is_mutable_pat spat
    | PBinding { mut; mode; var; typ; subpat } -> false
    | _ -> .

  let pgeneric_param span : generic_param -> string * SSP.AST.ty = function
    | { ident; kind; _ } -> (
        ( (plocal_ident ident),
          match kind with
          | GPType { default = Some t } -> pty span t
          | GPConst { typ = t } ->
              wrap_type_in_both "(fset [])" "(fset [])" (pty span t)
          | GPType { default = None } -> SSP.AST.WildTy
          | _ ->
              Error.unimplemented ~details:"SSProve: TODO: generic_params" span
        ))

  let pgeneric_param_as_argument span : generic_param -> SSP.AST.argument =
    function
    | { ident; kind; _ } ->
        SSP.AST.Implicit
          ( SSP.AST.Ident (plocal_ident ident),
            match kind with
            | GPType { default = Some t } -> pty span t
            | GPConst { typ = t } ->
                wrap_type_in_both "(fset [])" "(fset [])" (pty span t)
            | GPType { default = None } -> SSP.AST.WildTy
            | _ ->
                Error.unimplemented
                  ~details:"SSProve: TODO: generic_params_argument" span )

  let pgeneric_constraints_as_argument span :
      generic_constraint -> SSP.AST.argument list = function
    | GCType { bound = { trait; args }; _ } ->
        [
          (* SSP.AST.Typeclass (Some (SSP.ty_to_string (pty span typ) ^ "__" ^ String.concat ~sep:"~" bindings), SSP.AST.TypeTy); *)
          SSP.AST.Typeclass
            ( None,
              SSP.AST.AppTy
                ( SSP.AST.NameTy (pconcrete_ident trait),
                  List.map
                    ~f:(function
                      | GType typ -> pty span typ
                      | GConst { typ } ->
                          wrap_type_in_both "(fset [])" "(fset [])"
                            (pty span typ)
                      | _ ->
                          Error.unimplemented
                            ~details:"SSProve: TODO: generic_params_constraint1"
                            span)
                    args ) );
        ]
    | _ ->
        Error.unimplemented ~details:"SSProve: TODO: generic_params_constraint2"
          span

  let pgeneric (span : span) (generics : generics) : SSP.AST.argument list =
    List.map ~f:(pgeneric_param_as_argument span) generics.params
    @ List.concat_map
        ~f:(pgeneric_constraints_as_argument span)
        generics.constraints

  let pgeneric_implicit span generics : SSP.AST.argument list =
    List.map
      ~f:(fun v ->
        match v with
        | SSP.AST.Explicit (a, b) -> SSP.AST.Implicit (a, b)
        | _ -> v)
      (pgeneric span generics)

  let rec split_arrow_in_args (a : SSP.AST.ty) : SSP.AST.ty list * SSP.AST.ty =
    match a with
    | SSP.AST.Arrow (x, y) ->
        let l, r = split_arrow_in_args y in
        (x :: l, r)
    | _ -> ([], a)

  (* let rec wrap_type_in_enumerator (li : int -> string) (ii : int -> string) (i : int) (a : SSP.AST.ty) = *)
  (*   match a with *)
  (*   | SSP.AST.Arrow (x, y) -> *)
  (*     let size, x_val = wrap_type_in_enumerator li ii i x in *)
  (*     let size, y_val = wrap_type_in_enumerator li ii size y in *)
  (*     size, SSP.AST.Arrow (x_val, y_val) *)
  (*   | _ -> *)
  (*     i+1, wrap_type_in_both (li i) (ii i) a *)

  let rec wrap_type_in_enumerator_helper (li : int -> string)
      (ii : int -> string) (i : int) (a : SSP.AST.ty) =
    let l, r = split_arrow_in_args a in
    let size, t =
      List.fold_left
        ~f:(fun (yi, ys) x ->
          let size, x_val = wrap_type_in_enumerator_helper li ii yi x in
          ( size,
            match ys with
            | Some v -> Some (SSP.AST.Arrow (v, x_val))
            | None -> Some x_val ))
        ~init:(i, None) l
    in
    match t with
    | Some v -> (size, SSP.AST.Arrow (v, wrap_type_in_both (li i) (ii i) r))
    | None -> (size + 1, wrap_type_in_both (li i) (ii i) r)

  let wrap_type_in_enumerator (li : int -> string) (ii : int -> string)
      (a : SSP.AST.ty) (extra_L : string list) =
    let size, v = wrap_type_in_enumerator_helper li ii 0 a in
    (* Throw away anotation of last type, and replace with accumulation of all locations and imports *)
    let xs, a =
      match v with
      | SSP.AST.Arrow (x, SSP.AST.AppTy (SSP.AST.NameTy _, [ a ])) -> ([ x ], a)
      | SSP.AST.AppTy (SSP.AST.NameTy _, [ a ]) -> ([], a)
      | _ ->
          Error.unimplemented
            ~details:
              "SSProve: TODO: wrap_type_in_enumerator encountered an \
               unexpected type"
            (Span.dummy ())
    in
    let lis, iis =
      List.unzip (List.map ~f:(fun i -> (li i, ii i)) (List.range 0 size))
    in
    let lis = lis @ extra_L in
    let ret_ty =
      List.fold
        ~init:
          (wrap_type_in_both
             (let lis_str = String.concat ~sep:" :|: " lis in
              if List.length lis <= 1 then lis_str else "(" ^ lis_str ^ ")")
             (let iis_str = String.concat ~sep:" :|: " iis in
              if List.length iis <= 1 then iis_str else "(" ^ iis_str ^ ")")
             a)
        ~f:(fun y x -> SSP.AST.Arrow (x, y))
        xs
    in
    (size, ret_ty)

  let rec pitem (e : item) : SSP.AST.decl list =
    try pitem_unwrapped e
    with Diagnostics.SpanFreeError.Exn _kind ->
      [ SSP.AST.Unimplemented "item error backend" ]

  and pitem_unwrapped (e : AST.item) : SSP.AST.decl list =
    let span = e.span in
    (* let decls_from_attr = *)
    (*   List.map ~f:(fun { kind; span } -> *)
    (*       match kind with *)
    (*       | Tool { path; tokens } -> SSP.AST.Comment ("Tool" ^ ":" ^ " '" ^ path ^ "' " ^ "_" ^ " " ^ tokens) *)
    (*       | DocComment { kind; body } -> SSP.AST.Comment ("DocComment" ^ ":" ^ " " ^ body) *)
    (*     ) e.attrs *)
    (* in *)
    let decls_from_item =
      match e.v with
      | Fn { name = f_name; generics; body; params } ->
          loc_defs_from_name f_name
            (pgeneric_implicit span generics)
          @ [
            let (args, ret_typ) = lift_definition_type_to_both
                f_name
                (pgeneric span generics
                 @ List.map
                   ~f:(fun { pat; typ; typ_span; attrs } ->
                       SSP.AST.Explicit (ppat pat, pty span typ))
                   params)
                (pty span body.typ)
                []
            in
              SSP.AST.Equations
                   ( pconcrete_ident f_name,
                     args,
                     (pexpr
                        (extend_env_with_params
                           (Map.empty (module LocalIdent))
                           (List.map ~f:(fun { pat; typ; typ_span; attrs } -> pat) params))
                        true)
                       body,
                     ret_typ);
            ]
      | TyAlias { name; generics; ty } ->
          let g = pgeneric span generics in
          [
            (if List.is_empty g then
             SSP.AST.Notation
               ("'" ^ pconcrete_ident name ^ "'", SSP.AST.Type (pty span ty))
            else
              SSP.AST.Definition
                ( pconcrete_ident name,
                  g,
                  SSP.AST.Type (pty span ty),
                  SSP.AST.TypeTy ));
          ]
      (* record *)
      | Type
          {
            name;
            generics;
            variants = [ { name = record_name; arguments } ];
            is_struct = true;
          } ->
          (* [ *)
          (*   SSP.AST.Record *)
          (*     ( pconcrete_ident name (* ^ pconcrete_ident record_name *), *)
          (*       pgeneric span generics, *)
          (*       List.map *)
          (*         ~f:(fun (x, y) -> SSP.AST.Named (x, y)) *)
          (*         (p_record_record span arguments) ); *)
          (* ] *)
          let fields = p_record_record span arguments in
          let implicit_LI =
            [
              SSP.AST.Implicit
                ( SSP.AST.Ident "L",
                  (SSP.AST.NameTy "{fset Location}") );
              SSP.AST.Implicit
                (SSP.AST.Ident "I", (SSP.AST.NameTy "Interface"));
            ]
          in
          let ty_name =
            "("
            ^ String.concat ~sep:" "
                (pconcrete_ident name
                :: List.filter_map
                     ~f:(fun x ->
                       match x with
                       | SSP.AST.Explicit (p, t) ->
                           Some (SSP.pat_to_string p false 0)
                       | _ -> None)
                     (pgeneric span generics))
            ^ ")"
          in
          [
            SSP.AST.Definition
              ( pconcrete_ident name,
                pgeneric span generics,
                SSP.AST.Type (SSP.AST.Product (List.map ~f:snd fields)),
                SSP.AST.TypeTy );
          ]
          @ List.mapi
              ~f:(fun i (x, y) ->
                SSP.AST.Equations
                  ( x,
                    implicit_LI
                    @ pgeneric_implicit span generics
                    @ [
                        SSP.AST.Explicit
                          ( SSP.AST.Ident "s",
                            wrap_type_in_both "L" "I"
                              (SSP.AST.NameTy (pconcrete_ident name)) );
                      ],
                    SSP.AST.App
                      ( SSP.AST.Var "bind_both",
                        [
                          SSP.AST.Var "s";
                          SSP.AST.Lambda
                            ( [ SSP.AST.Ident "x" ],
                              SSP.AST.App
                                ( SSP.AST.Var "solve_lift",
                                  [
                                    SSP.AST.App
                                      ( SSP.AST.Var "ret_both",
                                        [
                                          SSP.AST.TypedTerm
                                            ( List.fold_right
                                                ~init:(SSP.AST.Var "x")
                                                ~f:(fun x y ->
                                                  SSP.AST.App
                                                    (SSP.AST.Var x, [ y ]))
                                                ((if i != 0 then [ "snd" ]
                                                 else [])
                                                @ List.init
                                                    (List.length fields - 1 - i)
                                                    (fun _ -> "fst")),
                                              y );
                                        ] );
                                  ] ) );
                        ] ),
                    wrap_type_in_both "L" "I" y ))
              fields
          @ [
              SSP.AST.Equations
                ( "Build_" ^ pconcrete_ident name,
                  List.mapi
                    ~f:(fun i _ ->
                      SSP.AST.Implicit
                        ( SSP.AST.Ident ("L" ^ Int.to_string i),
                          (SSP.AST.NameTy "{fset Location}") ))
                    fields
                  @ List.mapi
                      ~f:(fun i _ ->
                        SSP.AST.Implicit
                          ( SSP.AST.Ident ("I" ^ Int.to_string i),
                            (SSP.AST.NameTy "Interface") ))
                      fields
                  @ pgeneric_implicit span generics
                  @ List.mapi
                      ~f:(fun i (x, y) ->
                        SSP.AST.Implicit
                          ( SSP.AST.Ident x,
                            wrap_type_in_both
                              ("L" ^ Int.to_string i)
                              ("I" ^ Int.to_string i)
                              y ))
                      fields,
                  List.fold_left
                    ~init:
                      (SSP.AST.App
                         ( SSP.AST.Var "solve_lift",
                           [
                             SSP.AST.App
                               ( SSP.AST.Var "ret_both",
                                 [
                                   SSP.AST.TypedTerm
                                     ( SSP.AST.Tuple
                                         (List.map
                                            ~f:(fst >> fun x -> SSP.AST.Var x)
                                            fields),
                                       SSP.AST.NameTy ty_name );
                                 ] );
                           ] ))
                    ~f:(fun z (x, y) ->
                      SSP.AST.App
                        ( SSP.AST.Var "bind_both",
                          [
                            SSP.AST.Var x;
                            SSP.AST.Lambda ([ SSP.AST.Ident x ], z);
                          ] ))
                    fields,
                  let lis =
                    String.concat ~sep:":|:"
                      (List.map
                         ~f:(fun i -> "L" ^ Int.to_string i)
                         (List.range 0 (List.length fields)))
                  in
                  let lis =
                    match List.length fields with
                    | 0 -> "(fset [])"
                    | 1 -> lis
                    | _ -> "(" ^ lis ^ ")"
                  in
                  let iis =
                    String.concat ~sep:":|:"
                      (List.map
                         ~f:(fun i -> "I" ^ Int.to_string i)
                         (List.range 0 (List.length fields)))
                  in
                  let iis =
                    match List.length fields with
                    | 0 -> "(fset [])"
                    | 1 -> iis
                    | _ -> "(" ^ iis ^ ")"
                  in
                  SSP.AST.NameTy ("both" ^ " " ^ lis ^ " " ^ iis ^ " " ^ ty_name)
                )
              (* :: SSP.AST.Arguments ("Build_" ^ pconcrete_ident name,) *);
            ]
          @ List.mapi
              ~f:(fun i (x, y) ->
                SSP.AST.Notation
                  ( "'Build_"
                    ^ pconcrete_ident name
                    ^ "'" ^ " " ^ "'['" ^ " " ^ "x" ^ " " ^ "']'" ^ " " ^ "'('"
                    ^ " " ^ "'" ^ x ^ "'" ^ " " ^ "':='" ^ " " ^ "y" ^ " "
                    ^ "')'",
                    SSP.AST.App
                      ( SSP.AST.Var
                          ("Build_"
                          ^ pconcrete_ident name),
                        List.mapi
                          ~f:(fun j (x, y) ->
                            SSP.AST.AppFormat
                              ( [ x ^ " " ^ ":=" ^ " "; (*v*) "" ],
                                [
                                  SSP.AST.Value
                                    ( (if j == i then SSP.AST.Var "y"
                                      else
                                        SSP.AST.App
                                          (SSP.AST.Var x, [ SSP.AST.Var "x" ])),
                                      false );
                                ] ))
                          fields ) ))
              fields
      (* Definition t_Error : choice_type := t_ErrorKind × t_ErrorKind. *)
      (* (* Uncurry is Build_.. fn *) *)
      (* Equations Build_Error {L I} {f_kind1 : both L I t_ErrorKind} {f_kind2 : both L I t_ErrorKind} : both L I t_Error := *)
      (*   Build_Error (f_kind1 := x) (f_kind2 := y) := *)
      (*   bind_both x (fun x' => *)
      (*   bind_both y (fun y' => *)
      (*                  ret_both ((x', y') : t_Error))). *)
      (* Solve All Obligations with solve_ssprove_obligations. *)
      (* Fail Next Obligation. *)
      (* Definition f_kind1 (v : t_Error) := fst v. *)
      (* Definition f_kind2 (v : t_Error) := snd v. *)

      (* enum *)
      | Type { name; generics; variants } ->
          (* [ *)
          (*   (* SSP.AST.Inductive *) *)
          (*   (*   ( U.Concrete_ident_view.to_definition_name name, *) *)
          (*   (*     pgeneric span generics, *) *)
          (*   (*     p_inductive span variants name ); *) *)
          (* ] *)
          let number_of_cases = Int.to_string (List.length variants) in
          let implicit_LI =
            [
              SSP.AST.Implicit
                ( SSP.AST.Ident "L",
                  (SSP.AST.NameTy "{fset Location}") );
              SSP.AST.Implicit
                (SSP.AST.Ident "I", (SSP.AST.NameTy "Interface"));
            ]
          in
          SSP.AST.Definition
            ( (* "t_" ^ *) pconcrete_ident name,
              pgeneric span generics,
              SSP.AST.Type
                (SSP.AST.NameTy ("chFin (mkpos " ^ number_of_cases ^ ")")),
              SSP.AST.TypeTy )
          :: List.mapi variants
               ~f:(fun i { name = v_name; arguments; is_record } ->
                 SSP.AST.Equations
                   ( pconcrete_ident v_name,
                     implicit_LI @ pgeneric span generics,
                     SSP.AST.Var
                       ("solve_lift ret_both (fintype.Ordinal (n:="
                      ^ number_of_cases ^ ") (m:=" ^ Int.to_string i
                      ^ ") eq_refl : " ^ pconcrete_ident name ^ ")"),
                     if is_record then
                       SSP.AST.NameTy ("both L I " ^ pconcrete_ident name)
                     else
                       match arguments with
                       | [] ->
                           SSP.AST.NameTy ("both L I " ^ pconcrete_ident name)
                       | [ (arg_name, arg_ty, attr) ] ->
                           SSP.AST.AppTy
                             ( pty span arg_ty,
                               [
                                 SSP.AST.NameTy
                                   ("both L I " ^ pconcrete_ident name);
                               ] )
                       | _ ->
                           SSP.AST.Arrow
                             ( SSP.AST.Product
                                 (List.map
                                    ~f:((fun (x, y, z) -> y) >> pty span)
                                    arguments),
                               SSP.AST.NameTy
                                 ("both L I " ^ pconcrete_ident name) ) ))
      | Type { name; generics; variants } ->
          let g = pgeneric span generics in
          [
            (if List.is_empty g then
             SSP.AST.Notation
               ( "'" ^ "t_" ^ pconcrete_ident name ^ "'",
                 SSP.AST.Type
                   (SSP.AST.Product
                      (List.map ~f:snd (p_record span variants name))) )
            else
              SSP.AST.Definition
                ( "t_" ^ pconcrete_ident name,
                  g,
                  SSP.AST.Type
                    (SSP.AST.Product
                       (List.map ~f:snd (p_record span variants name))),
                  SSP.AST.TypeTy ));
            SSP.AST.Definition
              ( pconcrete_ident name,
                [
                  SSP.AST.Implicit
                    ( SSP.AST.Ident "L",
                      (SSP.AST.NameTy "{fset Location}") );
                  SSP.AST.Implicit
                    ( SSP.AST.Ident "I",
                      (SSP.AST.NameTy "Interface") );
                ],
                SSP.AST.Var "id",
                SSP.AST.Arrow
                  ( wrap_type_in_both "L" "I"
                      (SSP.AST.NameTy ("t_" ^ pconcrete_ident name)),
                    wrap_type_in_both "L" "I"
                      (SSP.AST.NameTy ("t_" ^ pconcrete_ident name)) ) );
          ]
      | IMacroInvokation { macro; argument; span } -> (
          let unsupported () =
            let id = [%show: concrete_ident] macro in
            let t = 0 / 0 in
            Error.raise { kind = UnsupportedMacro { id }; span = e.span }
          in
          match U.Concrete_ident_view.to_view macro with
          | { crate = "hacspec_lib"; path = _; definition = name } -> (
              match name with
              | "public_nat_mod" ->
                  let open Hacspeclib_macro_parser in
                  let o : PublicNatMod.t =
                    PublicNatMod.parse argument |> Result.ok_or_failwith
                  in
                  [
                    SSP.AST.Notation
                      ( "'" ^ "t_" ^ o.type_name ^ "'",
                        SSP.AST.Type
                          (SSP.AST.NatMod
                             ( o.type_of_canvas,
                               o.bit_size_of_field,
                               o.modulo_value )) );
                    SSP.AST.Definition
                      ( o.type_name,
                        [
                          SSP.AST.Implicit
                            ( SSP.AST.Ident "L",
                              (SSP.AST.NameTy "{fset Location}") );
                          SSP.AST.Implicit
                            ( SSP.AST.Ident "I",
                              (SSP.AST.NameTy "Interface") );
                        ],
                        SSP.AST.Var "id",
                        SSP.AST.Arrow
                          ( wrap_type_in_both "L" "I"
                              (SSP.AST.NameTy ("t_" ^ o.type_name)),
                            wrap_type_in_both "L" "I"
                              (SSP.AST.NameTy ("t_" ^ o.type_name)) ) );
                  ]
              | "bytes" ->
                  let open Hacspeclib_macro_parser in
                  let o : Bytes.t =
                    Bytes.parse argument |> Result.ok_or_failwith
                  in
                  [
                    SSP.AST.Notation
                      ( "'" ^ "t_" ^ o.bytes_name ^ "'",
                        SSP.AST.Type
                          (SSP.AST.ArrayTy
                             ( SSP.AST.Int { size = SSP.AST.U8; signed = false },
                               (* int_of_string *) o.size )) );
                    SSP.AST.Definition
                      ( o.bytes_name,
                        [
                          SSP.AST.Implicit
                            ( SSP.AST.Ident "L",
                              (SSP.AST.NameTy "{fset Location}") );
                          SSP.AST.Implicit
                            ( SSP.AST.Ident "I",
                              (SSP.AST.NameTy "Interface") );
                        ],
                        SSP.AST.Var "id",
                        SSP.AST.Arrow
                          ( wrap_type_in_both "L" "I"
                              (SSP.AST.NameTy ("t_" ^ o.bytes_name)),
                            wrap_type_in_both "L" "I"
                              (SSP.AST.NameTy ("t_" ^ o.bytes_name)) ) );
                  ]
              | "unsigned_public_integer" ->
                  let open Hacspeclib_macro_parser in
                  let o =
                    UnsignedPublicInteger.parse argument
                    |> Result.ok_or_failwith
                  in
                  [
                    SSP.AST.Notation
                      ( "'" ^ "t_" ^ o.integer_name ^ "'",
                        SSP.AST.Type
                          (SSP.AST.ArrayTy
                             ( SSP.AST.Int { size = SSP.AST.U8; signed = false },
                               Int.to_string ((o.bits + 7) / 8) )) );
                    SSP.AST.Definition
                      ( o.integer_name,
                        [
                          SSP.AST.Implicit
                            ( SSP.AST.Ident "L",
                              (SSP.AST.NameTy "{fset Location}") );
                          SSP.AST.Implicit
                            ( SSP.AST.Ident "I",
                              (SSP.AST.NameTy "Interface") );
                        ],
                        SSP.AST.Var "id",
                        SSP.AST.Arrow
                          ( wrap_type_in_both "L" "I"
                              (SSP.AST.NameTy ("t_" ^ o.integer_name)),
                            wrap_type_in_both "L" "I"
                              (SSP.AST.NameTy ("t_" ^ o.integer_name)) ) );
                  ]
              | "public_bytes" ->
                  let open Hacspeclib_macro_parser in
                  let o : Bytes.t =
                    Bytes.parse argument |> Result.ok_or_failwith
                  in
                  let typ =
                    SSP.AST.ArrayTy
                      ( SSP.AST.Int { size = SSP.AST.U8; signed = false },
                        (* int_of_string *) o.size )
                  in
                  [
                    SSP.AST.Notation
                      ("'" ^ "t_" ^ o.bytes_name ^ "'", SSP.AST.Type typ);
                    SSP.AST.Definition
                      ( o.bytes_name,
                        [
                          SSP.AST.Implicit
                            ( SSP.AST.Ident "L",
                              (SSP.AST.NameTy "{fset Location}") );
                          SSP.AST.Implicit
                            ( SSP.AST.Ident "I",
                              (SSP.AST.NameTy "Interface") );
                        ],
                        SSP.AST.Var "id",
                        SSP.AST.Arrow
                          ( wrap_type_in_both "L" "I"
                              (SSP.AST.NameTy ("t_" ^ o.bytes_name)),
                            wrap_type_in_both "L" "I"
                              (SSP.AST.NameTy ("t_" ^ o.bytes_name)) ) );
                  ]
              | "array" ->
                  let open Hacspeclib_macro_parser in
                  let o : Array.t =
                    Array.parse argument |> Result.ok_or_failwith
                  in
                  let typ =
                    match o.typ with
                    (* Some *)
                    | "U128" -> SSP.AST.U128
                    (* Some *)
                    | "U64" -> SSP.AST.U64
                    (* Some *)
                    | "U32" -> SSP.AST.U32
                    (* Some *)
                    | "U16" -> SSP.AST.U16
                    (* Some *)
                    | "U8" -> SSP.AST.U8
                    | _usize -> SSP.AST.U32 (* TODO: usize? *)
                  in
                  [
                    SSP.AST.Notation
                      ( "'" ^ "t_" ^ o.array_name ^ "'",
                        SSP.AST.Type
                          (SSP.AST.ArrayTy
                             ( SSP.AST.Int { size = typ; signed = false },
                               (* int_of_string *) o.size )) );
                    SSP.AST.Definition
                      ( o.array_name,
                        [
                          SSP.AST.Implicit
                            ( SSP.AST.Ident "L",
                              (SSP.AST.NameTy "{fset Location}") );
                          SSP.AST.Implicit
                            ( SSP.AST.Ident "I",
                              (SSP.AST.NameTy "Interface") );
                        ],
                        SSP.AST.Var "id",
                        SSP.AST.Arrow
                          ( wrap_type_in_both "L" "I"
                              (SSP.AST.NameTy ("t_" ^ o.array_name)),
                            wrap_type_in_both "L" "I"
                              (SSP.AST.NameTy ("t_" ^ o.array_name)) ) );
                  ]
              | _ -> unsupported ())
          | _ -> unsupported ())
      | Use { path; is_external; rename } ->
          let ns_crate, ns_path = ctx.current_namespace in
          if is_external then []
          else [ SSP.AST.Require (None, (* ns_crate:: ns_path @ *) path, rename) ]
      | HaxError s -> [ __TODO_item__ span s ]
      | NotImplementedYet -> [ __TODO_item__ span "Not implemented yet?" ]
      | Alias _ -> [ __TODO_item__ span "Not implemented yet? alias" ]
      | Trait { name; generics; items } ->
          [
            (* SSP.AST.Unimplemented (AST.show_item e); *)
            SSP.AST.Class
              ( pconcrete_ident name,
                (* List.map *)
                (*   ~f:(pgeneric_param_as_argument span) *)
                (*   (match List.rev generics.params with *)
                (*   | _ :: xs -> List.rev xs *)
                (*   | _ -> []) *)
                [],
                List.concat_map
                  ~f:(fun x ->
                    match x.ti_v with
                    | TIConst const_ty ->
                      [
                        SSP.AST.Named
                          (pconcrete_ident x.ti_ident,
                           wrap_type_in_both
                             "(fset[])"
                             "(fset[])"
                             (pty x.ti_span const_ty))
                      ]
                    | TIFn fn_ty ->
                        let loc_name = pconcrete_ident x.ti_ident ^ "_loc" in
                        let include_extra_loc =
                          match fn_ty with
                          | TArrow (inputs, output) -> true
                          | _ -> false
                        in
                        let size, value =
                          wrap_type_in_enumerator
                            (fun (i : int) -> "L" ^ Int.to_string (i + 1))
                            (fun (i : int) -> "I" ^ Int.to_string (i + 1))
                            (pty x.ti_span fn_ty)
                            (if include_extra_loc then [ loc_name ] else [])
                        in
                        (if include_extra_loc then
                         [
                           SSP.AST.Named
                             (loc_name, SSP.AST.NameTy "{fset Location}");
                         ]
                        else [])
                        @ [
                            SSP.AST.Named
                              ( pconcrete_ident x.ti_ident,
                                SSP.AST.Forall
                                  ( List.map
                                      ~f:(fun (i : int) ->
                                        "L" ^ Int.to_string (i + 1))
                                      (List.range 0 size)
                                    @ List.map
                                        ~f:(fun (i : int) ->
                                          "I" ^ Int.to_string (i + 1))
                                        (List.range 0 size),
                                    [],
                                    value ) );
                          ]
                    | TIType trait_refs ->
                        SSP.AST.Named (pconcrete_ident x.ti_ident, SSP.AST.TypeTy)
                        :: List.map
                             ~f:(fun tr ->
                               SSP.AST.Coercion
                                 ( pconcrete_ident x.ti_ident ^ "_"
                                   ^ pconcrete_ident tr.trait,
                                   SSP.AST.AppTy
                                     ( SSP.AST.NameTy (pconcrete_ident tr.trait),
                                       [ SSP.AST.NameTy (pconcrete_ident x.ti_ident) ] )
                                 ))
                             trait_refs
                    (* (match List.rev trait_refs with *)
                    (* | _ :: xs -> List.rev xs *)
                    (* | _ -> []) *))
                  items );
          ]
          @ List.concat_map
              ~f:(fun x ->
                match x.ti_v with
                | TIFn (TArrow (inputs, output)) ->
                    [ SSP.AST.HintUnfold (pconcrete_ident x.ti_ident ^ "_loc", None) ]
                | _ -> [])
              items
      | Impl { generics; self_ty; of_trait = name, gen_vals; items } ->
          List.concat_map
            ~f:(fun x ->
              loc_defs_from_name x.ii_ident (pgeneric_implicit span generics))
            items
          @ [
              SSP.AST.ProgramInstance
                ( pglobal_ident name,
                  pgeneric span generics,
                  pty span self_ty,
                  args_ty span gen_vals,
                  SSP.AST.InstanceDecls
                    (List.concat_map
                       ~f:(fun x ->
                           match x.ii_v with
                           | IIFn { body; params } ->
                             let mvars_ext_fset_str =
                               "fset" ^ " " ^ "["
                               ^ String.concat ~sep:";"
                                 (List.map
                                    ~f:(fun x -> (plocal_ident x) ^ "_loc")
                                    (match
                                       Map.find ctx.analysis_data.mut_var
                                         (U.Concrete_ident_view.to_definition_name x.ii_ident)
                                     with
                                     | Some (l, _) -> l
                                     | _ -> []))
                               ^ "]"
                             in
                             [
                               SSP.AST.InlineDef
                                 ( (pconcrete_ident x.ii_ident ^ "_loc"),
                                   [],
                                   SSP.AST.NameTerm mvars_ext_fset_str,
                                   SSP.AST.NameTy "{fset Location}" );
                               let args, ret_typ = lift_definition_type_to_both
                                   x.ii_ident
                                   (List.map
                                      ~f:(fun { pat; typ; typ_span; attrs } ->
                                          SSP.AST.Explicit (ppat pat, pty span typ))
                                      params)
                                   (pty span body.typ)
                                   (match
                                      Map.find ctx.analysis_data.mut_var (U.Concrete_ident_view.to_definition_name x.ii_ident)
                                    with
                                    | Some (_ :: _, _) -> []
                                    | _ -> [ "fset []" ])
                               in
                               SSP.AST.LetDef
                                 ((pconcrete_ident x.ii_ident),
                                  args,
                                  (pexpr (extend_env_with_params
                                            (Map.empty (module LocalIdent))
                                            (List.map ~f:(fun { pat; typ; typ_span; attrs } -> pat) params)) true) body,
                                  ret_typ
                                 )]
                           | IIConst { body } ->
                             [
                               SSP.AST.LetDef
                                 ( (pconcrete_ident x.ii_ident),
                                   [],
                                   (pexpr (Map.empty (module LocalIdent)) false) body,
                                   wrap_type_in_both "(fset [])" "(fset [])" (pty span body.typ) );
                             ]
                           | IIType ty ->
                             [
                               SSP.AST.LetDef
                                 ( (pconcrete_ident x.ii_ident),
                                   [],
                                   SSP.AST.Type (pty span ty),
                                   SSP.AST.TypeTy );
                             ])
                       items) );
            ]
          @ [ SSP.AST.HintUnfold (pglobal_ident name, Some (pty span self_ty)) ]
    in
    (* decls_from_attr @ *) decls_from_item

  and loc_defs_from_name (name : concrete_ident) generics : SSP.AST.decl list =
    List.map
      ~f:(fun ((x, x_ty), x_n) -> (* x_ty should not be (totally) resolved! *)
          SSP.AST.Definition
            ( (plocal_ident x) ^ "_loc",
              generics,
              SSP.AST.AppFormat (
                ["(";";";"%nat)"],
                [SSP.AST.Typing (pty (Span.dummy ()) x_ty);
                 SSP.AST.Value (SSP.AST.Literal (Int.to_string x_n), false)]),
              SSP.AST.NameTy "Location" ))
      (match Map.find ctx.analysis_data.mut_var (U.Concrete_ident_view.to_definition_name name) with
      | Some l -> snd l
      | None -> [])

  and new_arguments lis iis (arguments : SSP.AST.argument list) =
      List.map
        ~f:(fun x ->
            SSP.AST.Implicit
              (SSP.AST.Ident x, (SSP.AST.NameTy "{fset Location}")))
        lis
      @ List.map
        ~f:(fun x ->
            SSP.AST.Implicit (SSP.AST.Ident x, (SSP.AST.NameTy "Interface")))
        iis
      @ snd
        (List.fold_left ~init:(0, [])
           ~f:(fun (i, y) arg ->
               let f =
                 wrap_type_in_both
                   ("L" ^ Int.to_string (i + 1))
                   ("I" ^ Int.to_string (i + 1))
               in
               match arg with
               | Implicit (p, t) -> (i, y @ [ SSP.AST.Implicit (p, t) ])
               | Explicit (p, t) -> (i + 1, y @ [ SSP.AST.Explicit (p, f t) ])
               | Typeclass (so, t) -> (i, y @ [ SSP.AST.Typeclass (so, t) ]))
           arguments)

  and lift_definition_type_to_both
      (name : concrete_ident)
      (arguments : SSP.AST.argument list)
      (typ : SSP.AST.ty)
      (extra_L : string list) : SSP.AST.argument list * SSP.AST.ty =
    let lis, iis = get_lis_and_iis_both arguments in
    let new_args = new_arguments lis iis arguments in
    let return_typ = both_return_type_from_name lis iis name typ extra_L in
    ( new_args, return_typ )

  and both_return_type_from_name lis iis name typ (extra_L : string list) =
    let mvars_ext_L =
      match Map.find ctx.analysis_data.mut_var (U.Concrete_ident_view.to_definition_name name) with
      | Some (l, l2) when List.length l > 0 ->
        [
          "fset" ^ " " ^ "["
          ^ String.concat ~sep:";"
            (List.map ~f:(fun x -> (plocal_ident x) ^ "_loc") l)
          ^ "]";
        ]
      | _ -> []
    in
    let lis = lis @ mvars_ext_L @ extra_L in
    let iis = iis in
    wrap_type_in_both
      (let lis_str = String.concat ~sep:" :|: " lis in
       if List.length lis <= 1 then lis_str else "(" ^ lis_str ^ ")")
      (let iis_str = String.concat ~sep:" :|: " iis in
       if List.length iis <= 1 then iis_str else "(" ^ iis_str ^ ")")
      typ

  and get_lis_and_iis_both (arguments : SSP.AST.argument list) : string list * string list =
    let num_explicit_args =
      List.length
        (List.filter ~f:(function Explicit _ -> true | _ -> false) arguments)
    in
    let lis, iis =
      if num_explicit_args == 0 (* TODO: arguments that are updated? *) then
        ([ "L" ], [ "I" ])
      else
        List.unzip
          (List.map
             ~f:(fun i ->
                 ("L" ^ Int.to_string (i + 1), "I" ^ Int.to_string (i + 1)))
             (List.range 0 num_explicit_args))
    in
    ( lis, iis )

  and p_inductive span variants parrent_name : SSP.AST.inductive_case list =
    List.map variants ~f:(fun { name; arguments; is_record } ->
        if is_record then
          SSP.AST.InductiveCase
            ( pconcrete_ident name,
              SSP.AST.RecordTy
                (pconcrete_ident name, p_record_record span arguments) )
        else
          let name = pconcrete_ident name in
          match arguments with
          | [] -> SSP.AST.BaseCase name
          | [ (arg_name, arg_ty, _arg_attrs) ] ->
              SSP.AST.InductiveCase (name, pty span arg_ty)
          | _ ->
              SSP.AST.InductiveCase
                (name, SSP.AST.Product (List.map ~f:(snd3 >> pty span) arguments)))

  and p_record span variants parrent_name : (string * SSP.AST.ty) list =
    match variants with
    | { name; arguments = [ (arg_name, arg_ty, _arg_attrs) ] } :: xs ->
        (pconcrete_ident arg_name, pty span arg_ty)
        :: p_record span xs parrent_name
    | { name; arguments = [] } :: xs ->
        ("TODO FIELD?", __TODO_ty__ span "TODO")
        :: p_record span xs parrent_name
    | { name; arguments } :: xs ->
        ( pconcrete_ident name,
          SSP.AST.RecordTy (pconcrete_ident name, p_record_record span arguments)
        )
        :: p_record span xs parrent_name
    | _ -> []

  and p_record_record span arguments : (string * SSP.AST.ty) list =
    List.map
      ~f:(function
        | arg_name, arg_ty, _arg_attrs -> (pconcrete_ident arg_name, pty span arg_ty))
      arguments
end

module type S = sig
  val pitem : item -> SSP.AST.decl list
  val pgeneric : span -> generics -> SSP.AST.argument list
end

let make ctx =
  (module Make (struct
    let ctx = ctx
  end) : S)

let decls_to_string (decls : SSP.AST.decl list) : string =
  String.concat ~sep:"\n" (List.map ~f:SSP.decl_to_string decls)

let print_item (analysis_data : StaticAnalysis.analysis_data) (item : item) :
    SSP.AST.decl list =
  let (module Print) =
    make
      {
        current_namespace = U.Concrete_ident_view.to_namespace item.ident;
        analysis_data;
      }
  in
  Print.pitem item
(* List.map ~f:SSP.decl_to_string @@ Print.pitem item |> String.concat ~sep:"\n" *)

let cleanup_item_strings =
  List.map ~f:String.strip
  >> List.filter ~f:(String.is_empty >> not)
  >> String.concat ~sep:"\n\n"

module ConCert = struct
  let translate_concert_annotations (analysis_data : StaticAnalysis.analysis_data) (e : item) : SSP.AST.decl list =
    let (module Print) =
      make
        {
          current_namespace = U.Concrete_ident_view.to_namespace e.ident;
          analysis_data;
        }
    in
    match e.v with
    | Fn { name = f_name; generics; body; params } ->
      List.concat_map
        ~f:(fun { kind; span } ->
            match kind with
            | Tool { path; tokens } -> (
                let token_list = token_list tokens in
                match path with
                | "hax::init" ->
                  let contract =
                    strip_or_error "contract argument missing"
                      (get_argument "contract" token_list)
                      e.span
                  in
                  [
                    SSP.AST.Definition
                      ( "init_" ^ contract,
                        [
                          SSP.AST.Explicit
                            (SSP.AST.Ident "chain", SSP.AST.NameTy "Chain");
                          SSP.AST.Explicit
                            ( SSP.AST.Ident "ctx",
                              SSP.AST.NameTy "ContractCallContext" );
                          SSP.AST.Explicit
                            ( SSP.AST.Ident "st",
                                (SSP.AST.NameTy ("state_" ^ contract)) );
                        ],
                        SSP.AST.App
                          (SSP.AST.Var "ResultMonad.Ok", [ SSP.AST.Var "st" ]),
                        SSP.AST.AppTy
                          ( SSP.AST.NameTy "ResultMonad.result",
                            [
                                (SSP.AST.NameTy ("state_" ^ contract));
                              SSP.AST.NameTy "t_ParseError";
                            ] ) );
                  ]
                | "hax::receive" ->
                  let contract =
                    strip_or_error "contract argument missing"
                      (get_argument "contract" token_list)
                      e.span
                  in
                  let name =
                    strip_or_error "name argument missing"
                      (get_argument "name" token_list)
                      e.span
                  in
                  let parameter = get_argument "parameter" token_list in
                  (* let logger = get_argument "logger" token_list in *)
                  (* let payable = get_argument "payable" token_list in *)
                  let param_instances, param_list, count, param_vars = (match parameter with
                      | Some x ->
                        [SSP.AST.ProgramInstance (
                            "t_HasReceiveContext",
                            [],
                            SSP.AST.NameTy ("t_" ^ strip x),
                            [SSP.AST.NameTy ("t_" ^ strip x); SSP.AST.Unit],
                            SSP.AST.InstanceDecls [SSP.AST.InlineDef
                               ( "f_get",
                                 [SSP.AST.Explicit ( SSP.AST.Ident "x", (SSP.AST.WildTy) );
                                  SSP.AST.Implicit ( SSP.AST.Ident "L", (SSP.AST.NameTy "{fset Location}" : SSP.AST.ty) );
                                  SSP.AST.Implicit ( SSP.AST.Ident "I", (SSP.AST.NameTy "Interface" : SSP.AST.ty) )],
                                 SSP.AST.Var "(solve_lift (@ret_both (t_ParamType × t_Result x t_ParseError)) (tt, inr tt))",
                                 SSP.AST.WildTy );]);
                         SSP.AST.ProgramInstance
                           ("t_Sized",
                            [],
                            SSP.AST.NameTy ("t_" ^ strip x),
                            [SSP.AST.NameTy ("t_" ^ strip x)],
                            SSP.AST.TermDef (SSP.AST.Lambda ( [SSP.AST.Ident "x"], SSP.AST.Ident "x")),
                        [
                          SSP.AST.Explicit
                            (SSP.AST.Ident "ctx", wrap_type_in_both "L0" "I0" (SSP.AST.NameTy ("t_" ^ strip x)));
                        ], 1, [ SSP.AST.Var "ctx" ]
                      | _ -> [], [], 0, [])
                  in
                  param_instances @
                  [
                    SSP.AST.Definition
                      ( "receive_" ^ contract ^ "_" ^ name,
                        Print.pgeneric span generics
                        @ List.map
                          ~f:(fun x ->
                              SSP.AST.Implicit
                                (SSP.AST.Ident x, (SSP.AST.NameTy "{fset Location}" : SSP.AST.ty)))
                          (List.map ~f:(fun i -> "L" ^ Int.to_string i) (List.range 0 (count+1)))
                        @ List.map
                          ~f:(fun x ->
                              SSP.AST.Implicit
                                (SSP.AST.Ident x, (SSP.AST.NameTy "Interface" : SSP.AST.ty)))
                          (List.map ~f:(fun i -> "I" ^ Int.to_string i) (List.range 0 (count+1)))
                        @ param_list
                        @ [
                          SSP.AST.Explicit
                            ( SSP.AST.Ident "st",
                              wrap_type_in_both ("L" ^ Int.to_string count) ("I" ^ Int.to_string count)
                                (SSP.AST.NameTy ("state_" ^ contract)) );
                          (* TODO: L, I *)
                        ],
                        (* Arguments *)
                        SSP.AST.App
                          ( SSP.AST.Var (pconcrete_ident f_name) (* contract *),
                            param_vars @ [ SSP.AST.Var "st" ] ),
                        wrap_type_in_both "_" "_"
                          (SSP.AST.NameTy
                             ("t_Result ((v_A × state_" ^ contract
                              ^ ")) (t_ParseError)")) );
                    (* TODO: L , I *)
                  ]
                | _ -> [])
            | _ -> [])
        e.attrs
     | Type
        {
          name;
          generics;
          variants = [ { name = record_name; arguments } ];
          is_struct = true;
        } ->
      List.concat_map
        ~f:(fun { kind; span } ->
            match kind with
            | Tool { path; tokens } when String.equal path "hax::contract_state"
              ->
              let token_list = token_list tokens in
              let contract =
                strip_or_error "contract argument missing"
                  (get_argument "contract" token_list)
                  e.span
              in
              [
                SSP.AST.Definition
                  ( "state_" ^ contract,
                    [],
                    SSP.AST.Var (pconcrete_ident name),
                    SSP.AST.TypeTy );
                (* SSP.AST.ProgramInstance *)
                (*   (\* string * argument list * ty * ty list * definition_type *\) *)
                (*   ( "Serializable", *)
                (*     [], *)
                (*     SSP.AST.NameTy ("state_" ^ contract), *)
                (*     [], *)
                (*     [ *)
                (*       SSP.AST.InlineDef *)
                (*         ( "serialize", *)
                (*           [], *)
                (*           SSP.AST.Var "serialize_value_term", *)
                (*           SSP.AST.NameTy "serialize_type" ); *)
                (*       SSP.AST.InlineDef *)
                (*         ( "deserialize", *)
                (*           [], *)
                (*           SSP.AST.Var "deserialize_value_term", *)
                (*           SSP.AST.NameTy "deserialize_type" ); *)
                (*     ] ); *)
              ]
            | _ -> [])
        e.attrs
    | _ -> []

  let concert_contract_type_decls (items : item list) : SSP.AST.decl list list =
    (* List.dedup_and_sort ~compare:String.compare *)
    let contract_items =
      (List.filter_map
         ~f:(function
             | { kind = Tool { path; tokens }; span }
               when String.equal path "hax::receive" ->
               let token_list = token_list tokens in
               let contract =
                 strip_or_error "contract argument missing"
                   (get_argument "contract" token_list)
                   (Span.dummy ())
                   (* TODO: carry span information *)
               in
               let name =
                 strip_or_error "name argument missing"
                   (get_argument "name" token_list)
                   (Span.dummy ())
                   (* TODO: carry span information *)
               in
               let parameter = get_argument "parameter" token_list in
               Some (contract, parameter, name)
             | _ -> None)
         (List.concat_map ~f:(fun x -> x.attrs) items)) in
    if List.length contract_items == 0
    then []
    else
      let contract_map =
        List.fold_left
          ~init:(Map.empty (module String))
          ~f:(fun y (x_name, x_parameter, x_item) ->
              Map.set y ~key:x_name
                ~data:
                  (Option.value ~default:[] (Map.find y x_name)
                   @ [ (x_parameter, x_item) ]))
          contract_items
      in
      List.map
        ~f:(fun contract ->
            let receive_functions : (_ * string) list =
              Option.value ~default:[] (Map.find contract_map contract)
            in
            [
              SSP.AST.Inductive
                ( "Msg_" ^ contract,
                  [],
                  List.map
                    ~f:(function
                        | Some param, x_item ->
                          SSP.AST.InductiveCase
                            ( "msg_" ^ contract ^ "_" ^ x_item,
                              SSP.AST.NameTy ("t_" ^ strip param) )
                        | None, x_item ->
                          SSP.AST.BaseCase ("msg_" ^ contract ^ "_" ^ x_item))
                    receive_functions );
              SSP.AST.ProgramInstance ("t_HasReceiveContext",
                                [],
                                SSP.AST.NameTy ("state_" ^ contract),
                                [SSP.AST.NameTy ("state_" ^ contract); SSP.AST.Unit],
                                SSP.AST.InstanceDecls [SSP.AST.InlineDef
                               ( "get",
                                 [SSP.AST.Explicit ( SSP.AST.Ident "x", (SSP.AST.WildTy) );
                                  SSP.AST.Implicit ( SSP.AST.Ident "L", (SSP.AST.NameTy "{fset Location}" : SSP.AST.ty) );
                                  SSP.AST.Implicit ( SSP.AST.Ident "I", (SSP.AST.NameTy "Interface" : SSP.AST.ty) )],
                                 SSP.AST.Var "(solve_lift (@ret_both (t_ParamType × t_Result x t_ParseError)) (tt, inr tt))",
                                 SSP.AST.WildTy );]);
              SSP.AST.ProgramInstance ("t_Sized",
                                [],
                                SSP.AST.NameTy ("state_" ^ contract),
                                [SSP.AST.NameTy ("state_" ^ contract)],
                               SSP.AST.TermDef (SSP.AST.Lambda ( [SSP.AST.Ident "x"], SSP.AST.Ident "x")));
              SSP.AST.ProgramInstance ("t_HasActions",
                                [],
                                SSP.AST.NameTy ("state_" ^ contract),
                                [SSP.AST.NameTy ("state_" ^ contract)],
                                SSP.AST.TermDef (SSP.AST.Var "Admitted"));
              SSP.AST.Equations
                ( "receive_" ^ contract,
                  [
                    SSP.AST.Explicit (SSP.AST.Ident "chain", SSP.AST.NameTy "Chain");
                    SSP.AST.Explicit
                      (SSP.AST.Ident "ctx", SSP.AST.NameTy "ContractCallContext");
                    SSP.AST.Explicit
                      ( SSP.AST.Ident "st", (SSP.AST.NameTy ("state_" ^ contract)) );
                    SSP.AST.Explicit
                      ( SSP.AST.Ident "msg",
                        SSP.AST.NameTy ("Datatypes.option Msg_" ^ contract) );
                  ],
                  SSP.AST.Match
                    ( SSP.AST.Var "msg",
                      List.map
                        ~f:(function
                            | Some param, x_item ->
                              ( SSP.AST.Ident
                                  ("Some" ^ " " ^ "(" ^ "msg_" ^ contract ^ "_" ^ x_item
                                   ^ " " ^ "val" ^ ")"),
                                SSP.AST.Var
                                  ("match (is_pure (both_prog (receive_" ^ contract
                                   ^ "_" ^ x_item
                                   ^ " (ret_both val) (ret_both st)))) with\n\
                                     \         | inl x => ResultMonad.Ok (\
                                      (fst x), [])\n\
                                     \         | inr x => ResultMonad.Err x\n\
                                     \         end") )
                            | None, x_item ->
                              ( SSP.AST.Ident
                                  ("Some" ^ " " ^ "msg_" ^ contract ^ "_" ^ x_item),
                                SSP.AST.Var
                                  ("match (is_pure (both_prog (receive_" ^ contract
                                   ^ "_" ^ x_item
                                   ^ " (ret_both st)))) with\n\
                                     \         | inl x => ResultMonad.Ok (\
                                      (fst x), [])\n\
                                     \         | inr x => ResultMonad.Err x\n\
                                     \         end") ))
                        receive_functions
                      @ [ (SSP.AST.WildPat, SSP.AST.Var "ResultMonad.Err tt") ] ),
                  SSP.AST.NameTy
                    ("ResultMonad.result (state_" ^ contract
                     ^ " * list ActionBody) t_ParseError") );
              SSP.AST.ProgramInstance ("Serializable",
                                [],
                                SSP.AST.NameTy ("state_" ^ contract),
                                [SSP.AST.NameTy ("state_" ^ contract)],
                                SSP.AST.InstanceDecls[]);
              SSP.AST.ProgramInstance (
                "Serializable",
                [],
                SSP.AST.NameTy ("Msg_" ^ contract),
                [SSP.AST.NameTy ("Msg_" ^ contract)],
                SSP.AST.TermDef (SSP.AST.Var ("Derive Serializable Msg_OVN_rect<" ^ String.concat ~sep:"," (List.map ~f:(fun x -> "msg_" ^ contract ^ "_" ^ snd x) receive_functions) ^ ">")));
              SSP.AST.Definition
                ( "contract_" ^ contract,
                  [],
                  SSP.AST.App
                    ( SSP.AST.Var "build_contract",
                      [
                        SSP.AST.Var ("init_" ^ contract);
                        SSP.AST.Var ("receive_" ^ contract);
                      ] ),
                  SSP.AST.AppTy
                    ( SSP.AST.NameTy "Contract",
                      [
                        (SSP.AST.NameTy ("state_" ^ contract));
                        SSP.AST.NameTy ("Msg_" ^ contract);
                        (SSP.AST.NameTy ("state_" ^ contract));
                        SSP.AST.NameTy "t_ParseError";
                      ] ) );
            ])
        (Map.keys contract_map)

  let concert_header =
    [SSP.AST.Comment "Concert lib part";
     SSP.AST.Require (Some "ConCert.Utils", ["Extras"], None);
     SSP.AST.Require (Some "ConCert.Utils", ["Automation"], None);
     SSP.AST.Require (Some "ConCert.Execution", ["Serializable"], None);
     SSP.AST.Require (Some "ConCert.Execution", ["Blockchain"], None);
     SSP.AST.Require (Some "ConCert.Execution", ["ContractCommon"], None);
     SSP.AST.Require (Some "ConCert.Execution", ["Serializable"], None);
     SSP.AST.Require (None, ["ConCertLib"], None)]
end

let process_annotation (x : 'a list) (f2 : ('b * ('a -> 'b)) list) :
    'b list =
  List.concat_map ~f:(fun (d, f) ->
      let temp = List.map ~f:f x in
      if List.length (List.concat temp) == 0
      then []
      else d :: temp) f2

  (* List.fold_left ~init:(List.map ~f:f1 x) *)
  (*   ~f:(fun y f -> List.map ~f:(fun (x, y) -> y @ f x) (List.zip_exn x y)) *)
  (*   f2 *)

let string_of_items (x, y) =
  cleanup_item_strings
    (List.map ~f:decls_to_string
       (process_annotation x
          [([], print_item y);
           (ConCert.(concert_header, translate_concert_annotations y))]
        @ ConCert.concert_contract_type_decls x))

(* TODO move into string_of_items, as SSP.AST decl *)
let hardcoded_coq_headers =
  "(* File automatically generated by Hacspec *)\n\
   Set Warnings \"-notation-overridden,-ambiguous-paths\".\n\
   From Crypt Require Import choice_type Package Prelude.\n\
   Import PackageNotation.\n\
   From extructures Require Import ord fset.\n\
   From mathcomp Require Import word_ssrZ word.\n\
   From Jasmin Require Import word.\n\n\
   From Coq Require Import ZArith.\n\
   From Coq Require Import Strings.String.\n\
   Import List.ListNotations.\n\
   Open Scope list_scope.\n\
   Open Scope Z_scope.\n\
   Open Scope bool_scope.\n\n\
   From Hacspec Require Import ChoiceEquality.\n\
   From Hacspec Require Import LocationUtility.\n\
   From Hacspec Require Import Hacspec_Lib_Comparable.\n\
   From Hacspec Require Import Hacspec_Lib_Pre.\n\
   From Hacspec Require Import Hacspec_Lib.\n\n\
   Open Scope hacspec_scope.\n\
   Import choice.Choice.Exports.\n\n\
   Obligation Tactic := (* try timeout 8 *) solve_ssprove_obligations.\n"

let translate (bo : BackendOptions.t) (items : AST.item list) : Types.file list
    =
  let analysis_data = StaticAnalysis.analyse () items in
  U.group_items_by_namespace items
  |> Map.to_alist
  |> List.map ~f:(fun (ns, items) ->
         let mod_name =
           String.concat ~sep:"_"
             (List.map
                ~f:(map_first_letter String.uppercase)
                (fst ns :: snd ns))
         in

         Types.
           {
             path = mod_name ^ ".v";
             contents =
               hardcoded_coq_headers ^ "\n"
               ^ string_of_items (items, analysis_data)
               ^ "\n";
           })

let apply_phases (bo : BackendOptions.t) (i : Ast.Rust.item list) :
    AST.item list =
  TransformToInputLanguage.ditems i

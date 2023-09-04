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
             (* and type state_passing_loop = Features.Off.state_passing_loo *)
   ) =
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
    let int_repr (x : string) (i : string) : string =
      i (* "i" ^ x ^ "(" ^ i ^ ")" *)

    let let_stmt (var : string) (expr : string) (typ : string) (body : string)
        (depth : int) : string =
      "letb" ^ " " ^ var ^ " " ^ ":="
      ^ " " ^ expr ^ " "
      (* ^ " (" ^ expr ^ ") "  *)
      ^ ":of:" ^ " " ^ typ
      (* ^ ":" ^ " " *)
      (* ^ "both _ _" ^ " " ^ "(" ^ typ ^ ")" *)
      ^ " " ^ "in" ^ newline_indent depth
      ^ body

    let let_mut_stmt (var : string) (expr : string) (typ : string)
        (body : string) (depth : int) : string =
      "letbm" ^ " " ^ var ^ " " ^ "loc(" ^ var ^ "_loc" ^ ")" ^ " " ^ ":="
      (* ^ " (" ^ expr ^ ") " ^ ":" ^ " " ^ "both _ _" ^ " " ^ "(" ^ typ ^ ")" *)
      ^ " " ^ expr ^ " " ^ ":of:" ^ " " ^ typ
      ^ " " ^ "in" ^ newline_indent depth ^ body

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

let token_list (tokens : string) : (string list) list =
  List.map ~f:(split_str ~on:"=") (split_str ~on:"," tokens)

let get_argument (s : string) (token_list : (string list) list) =
  (List.find_map ~f:(function | [v; a] when String.equal (String.strip v) s -> Some a | _ -> None) token_list)

let strip (x : string) =
  String.strip ?drop:(Some (function | '\"' -> true | _ -> false)) (String.strip x)

let strip_or_error (err : string) (s : string option) (span) =
  (match s with
   | Some x -> strip x
   | None -> Error.unimplemented ~details:err span)

module Make (Ctx : sig
  val ctx : Context.t
end) =
struct
  open Ctx

  let pconcrete_ident (id : concrete_ident) : string =
    U.Concrete_ident_view.to_definition_name id
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

  let wrap_type_in_both (l : string) (i : string) (a : SSP.AST.ty) =
    SSP.AST.AppTy (SSP.AST.NameTy ("both" ^ " " ^ l ^ " " ^ i), [ a ])

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
            ^ SSP.term_to_string_with_paren (pexpr false length) 0
            ^ ")" ^ ")" )
        (* TODO: check int.to_string is correct! *)
    | TSlice { ty; _ } -> SSP.AST.SliceTy (pty span ty)
    | TParam i -> SSP.AST.NameTy i.name
    | TAssociatedType s -> SSP.AST.WildTy
    | TOpaque _ -> __TODO_ty__ span "pty: TAssociatedType/TOpaque"
    | _ -> .

  and args_ty span (args : generic_value list) : SSP.AST.ty list =
    (* List.map ~f:pty *)
    match args with
    | arg :: xs ->
        (match arg with
        | GLifetime { lt; witness } -> __TODO_ty__ span "lifetime"
        | GType typ -> pty span typ
        | GConst {typ; _} -> wrap_type_in_both "(fset [])" "(fset [])" (pty span typ))
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
        SSP.AST.Ident var.name
    | PBinding
        {
          mut = Mutable _;
          mode = _;
          subpat;
          (* TODO no subpat? *)
          var;
          typ = _ (* we skip type annot here *);
        } ->
        SSP.AST.Ident var.name (* TODO Mutable binding ! *)
    | PArray { args } -> __TODO_pat__ p.span "Parray?"
    | PConstruct { name = `TupleCons 0; args = [] } -> SSP.AST.UnitPat
    | PConstruct { name = `TupleCons 1; args = [ { pat } ] } ->
        __TODO_pat__ p.span "tuple 1"
    | PConstruct { name = `TupleCons n; args } ->
        SSP.AST.TuplePat (List.map ~f:(fun { pat } -> ppat pat) args)
    | PConstruct { name; args; is_record = true } ->
        SSP.AST.RecordPat (pglobal_ident name, pfield_pats args)
    | PConstruct { name; args; is_record = false } ->
        SSP.AST.ConstructorPat
          (pglobal_ident name, List.map ~f:(fun p -> ppat p.pat) args)
    | PConstant { lit } -> SSP.AST.Lit (pliteral lit)
    | PDeref { subpat } -> __TODO_pat__ p.span "deref"
    | _ -> .

  and pfield_pats (args : field_pat list) : (string * SSP.AST.pat) list =
    match args with
    | { field; pat } :: xs -> (pglobal_ident field, ppat pat) :: pfield_pats xs
    | _ -> []

  and pexpr (add_solve : bool) (e : expr) : SSP.AST.term =
    let span = e.span in
    (match (add_solve, e.e) with
    | true, (Construct { is_record = true; _ }
    | If _
    | Match _
    | Literal _
    | Construct { constructor = `TupleCons _; _ }
    | App _
    | GlobalVar _
    | LocalVar _) ->
        fun x -> SSP.AST.App (SSP.AST.Var "solve_lift", [ x ])
    | _ -> fun x -> x)
      (match e.e with
      | Literal lit ->
          SSP.AST.App
            ( SSP.AST.Var "ret_both",
              [
                SSP.AST.TypedTerm (SSP.AST.Const (pliteral lit), pty span e.typ);
              ] )
          (* SSP.AST.TypedTerm (SSP.AST.App (SSP.AST.Var "ret_both", [ SSP.AST.TypedTerm (SSP.AST.Const (pliteral lit), pty span e.typ) ]), SSP.AST.AppTy (SSP.AST.NameTy ("both (fset []) ([interface])"), [SSP.AST.WildTy])) *)
      | LocalVar local_ident -> SSP.AST.NameTerm local_ident.name
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
          let args = List.map ~f:(pexpr false) args in
          SSP.AST.AppFormat (op, args)
      (* | App { f = { e = GlobalVar x }; args } -> *)
      (*    __TODO_term__ span "GLOBAL APP?" *)
      | App { f; args } ->
          let base = (pexpr false) f in
          let args = List.map ~f:(pexpr false) args in
          SSP.AST.App (base, args)
      | If { cond; then_; else_ } ->
          SSP.AST.If
            ( (pexpr false) cond,
              (pexpr false) then_,
              Option.value_map else_ ~default:(SSP.AST.Literal "()")
                ~f:(pexpr false) )
      | Array l -> SSP.AST.Array (List.map ~f:(pexpr add_solve) l)
      | Let { lhs; rhs; body; monadic } ->
          SSP.AST.Let
            {
              pattern = ppat lhs;
              mut = is_mutable_pat lhs;
              value = (pexpr false) rhs;
              body = (pexpr add_solve) body;
              value_typ = pty lhs.span lhs.typ;
            }
      | EffectAction _ -> __TODO_term__ span "monadic action"
      | Match { scrutinee; arms } ->
          SSP.AST.Match
            ( (pexpr false) scrutinee,
              List.map
                ~f:(fun { arm = { arm_pat; body } } ->
                  (ppat arm_pat, (pexpr false) body))
                arms )
      | Ascription { e; typ } -> __TODO_term__ span "asciption"
      | Construct { constructor = `TupleCons 1; fields = [ (_, e) ]; base } ->
          (pexpr false) e
      | Construct { constructor = `TupleCons n; fields; base } ->
          SSP.AST.App
            ( SSP.AST.Var "prod_b",
              [ SSP.AST.Tuple (List.map ~f:(snd >> pexpr false) fields) ] )
      | Construct { is_record = true; constructor; fields; base } ->
          SSP.AST.RecordConstructor
            ( SSP.AST.Var (pglobal_ident constructor),
              List.map
                ~f:(fun (f, e) -> (pglobal_ident f, (pexpr false) e))
                fields )
      | Construct { constructor; fields = [ (f, e) ]; base } ->
          SSP.AST.App
            (SSP.AST.Var (pglobal_ident constructor), [ (pexpr add_solve) e ])
      | Construct { constructor; fields; base } ->
          (* __TODO_term__ span "constructor" *)
          SSP.AST.App
            ( SSP.AST.Var (pglobal_ident constructor),
              List.map ~f:(snd >> pexpr add_solve) fields )
      | Closure { params; body } ->
          SSP.AST.Lambda (List.map ~f:ppat params, (pexpr add_solve) body)
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
          (pexpr add_solve)
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
                (pexpr add_solve) start;
                (pexpr add_solve) end_;
                SSP.AST.Lambda
                  ( [ SSP.AST.Ident "{L I _ _}"; SSP.AST.Ident var.name ],
                    SSP.AST.App
                      ( SSP.AST.Var "ssp",
                        [
                          SSP.AST.Lambda ([ ppat bpat ], (pexpr true) body);
                        ] ) );
                (pexpr add_solve) init;
              ] )
      | Loop
          {
            body;
            kind = ForLoop { pat; it; _ };
            state = Some { init; bpat; _ };
            label;
            _;
          } ->
          SSP.AST.App
            ( SSP.AST.Var "foldi_both_list",
              [
                (pexpr add_solve) it;
                SSP.AST.Lambda
                  ( [ SSP.AST.Ident "{L I _ _}"; ppat pat ],
                    SSP.AST.App
                      ( SSP.AST.Var "ssp",
                        [
                          SSP.AST.Lambda ([ ppat bpat ], (pexpr true) body);
                        ] ) );
                (pexpr add_solve) init;
              ] )
      | Loop { body; kind; state; label; _ } ->
          SSP.AST.Const (SSP.AST.Const_string ("other loop" ^ " todo(term)"))
      (* __TODO_term__ span "other loop" *)
      (* | Break { e; _ } -> *)
      (*     SSP.AST.Const (SSP.AST.Const_string ("break" ^ " todo(term)")) *)
      (*     (\* __TODO_term__ span "break" *\) *)
      | _ -> .)

  and is_mutable_pat pat =
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
    | PDeref { subpat; witness } -> is_mutable_pat subpat
    | PConstant { lit } -> false
    | PBinding { mut = Mutable _ } -> true
    | PBinding { mut; mode; var; typ; subpat = Some (spat, _) } ->
        is_mutable_pat spat
    | PBinding { mut; mode; var; typ; subpat } -> false

  let pgeneric_param span : generic_param -> string * SSP.AST.ty = function
    | { ident; kind; _ } ->
      ( ident.name,
        match kind with
        | GPType { default = Some t } -> pty span t
        | GPConst { typ = t } -> wrap_type_in_both "(fset [])" "(fset [])" (pty span t)
        | GPType { default = None } -> SSP.AST.WildTy
        | _ -> Error.unimplemented ~details:"SSProve: TODO: generic_params" span)

  let pgeneric_param_as_argument span : generic_param -> SSP.AST.argument =
    function
    | { ident; kind; _ } ->
      SSP.AST.Implicit (
        SSP.AST.Ident ident.name,
        match kind with
        | GPType { default = Some t } -> pty span t
        | GPConst { typ = t } -> wrap_type_in_both "(fset [])" "(fset [])" (pty span t)
        | GPType { default = None } -> SSP.AST.WildTy
        | _ -> Error.unimplemented ~details:"SSProve: TODO: generic_params_argument" span)

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
                        | GConst { typ } -> wrap_type_in_both "(fset [])" "(fset [])" (pty span typ)
                        | _ ->
                          Error.unimplemented
                            ~details:"SSProve: TODO: generic_params_constraint1" span)
                    args ) );
        ]
    | _ -> Error.unimplemented ~details:"SSProve: TODO: generic_params_constraint2" span

  let pgeneric span generics : SSP.AST.argument list =
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

  let rec wrap_type_in_enumerator_helper (li : int -> string) (ii : int -> string)
      (i : int) (a : SSP.AST.ty) =
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
    | Some v ->
        ( size,
          SSP.AST.Arrow
            ( v,
              wrap_type_in_both (li i) (ii i)
                r ) )
    | None -> (size + 1, wrap_type_in_both (li i) (ii i) r)

  let wrap_type_in_enumerator (li : int -> string) (ii : int -> string) (a : SSP.AST.ty) (extra_L : string list) =
    let size, v = wrap_type_in_enumerator_helper li ii 0 a in
    (* Throw away anotation of last type, and replace with accumulation of all locations and imports *)
    let xs, a = match v with
      | SSP.AST.Arrow (x, SSP.AST.AppTy (SSP.AST.NameTy _, [ a ])) -> ([x], a)
      | SSP.AST.AppTy (SSP.AST.NameTy _, [ a ]) -> ([], a)
      | _ -> Error.unimplemented ~details:"SSProve: TODO: wrap_type_in_enumerator encountered an unexpected type" (Span.dummy ())
    in
    let lis, iis = List.unzip (List.map ~f:(fun i -> (li i, ii i)) (List.range 0 size)) in
    let lis = lis @ extra_L in
    let ret_ty = List.fold
        ~init:(wrap_type_in_both
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
    let decls_from_attr =
      List.map ~f:(fun { kind; span } ->
          match kind with
          | Tool { path; tokens } -> SSP.AST.Comment ("Tool" ^ ":" ^ " '" ^ path ^ "' " ^ "_" ^ " " ^ tokens)
          | DocComment { kind; body } -> SSP.AST.Comment ("DocComment" ^ ":" ^ " " ^ body)
        ) e.attrs
    in
    let decls_from_item =
    match e.v with
    | Fn { name = f_name; generics; body; params } ->
        let ndep =
          []
          (* match Map.find (fst ctx.func_dep) name with *)
          (* | Some l -> l *)
          (* | None -> [] *)
          (* Not relevant yet *)
        in
        let (mvars_ext, mvars_loc)
              : local_ident list * (local_ident * AST.ty * int) list =
          match
            Map.find
              (ctx.analysis_data.mut_var
                : (local_ident list * ((local_ident * AST.ty) * int) list)
                  Map.M(Concrete_ident).t)
              f_name
          with
          | Some l ->
              ( fst l,
                List.map ~f:(fun ((x, x_ty), x_n) -> (x, x_ty, x_n)) (snd l) )
          | None -> ([], [])
        in
        let mvars_str =
          let generalized_L =
            match params with
            | [] -> ""
            | x :: xs ->
                List.fold_left
                  ~f:(fun y x -> y ^ ":|:" ^ "L" ^ Int.to_string (x + 1))
                  ~init:"L1"
                  (List.init (List.length xs) (fun x -> x + 1))
          in
          "("
          ^ (match (params, mvars_ext) with
            | _ :: _, [] -> generalized_L
            | _, _ ->
                (match params with [] -> "" | _ -> generalized_L ^ " :|: ")
                ^ "fset ["
                ^ String.concat ~sep:"; "
                    (List.map ~f:(fun x -> x.name ^ "_loc") mvars_ext)
                ^ "]")
          ^ ")"
        in
        let ndep_str =
          let generalized_I =
            match params with
            | [] -> ""
            | x :: xs ->
                List.fold_left
                  ~f:(fun y x -> y ^ ":|:" ^ "I" ^ Int.to_string (x + 1))
                  ~init:"I1"
                  (List.init (List.length xs) (fun x -> x + 1))
          in
          "("
          ^ (match (params, ndep) with
            | _ :: _, [] -> generalized_I
            | _, _ ->
                (match params with [] -> "" | _ -> generalized_I ^ " :|: ")
                ^ "[interface "
                ^ String.concat ~sep:"; " (List.map ~f:pconcrete_ident ndep)
                ^ "]")
          ^ ")"
        in
        List.fold_left ~init:[]
          ~f:(fun y (x, x_ty, x_n) ->
            SSP.AST.Definition
              ( x.name ^ "_loc",
                pgeneric_implicit span generics,
                SSP.AST.Const
                  (SSP.AST.Const_string
                     ("("
                     ^ SSP.ty_to_string (pty (Span.dummy ()) x_ty)
                     ^ " ; " ^ Int.to_string x_n ^ "%nat)")),
                SSP.AST.NameTy "Location" )
            :: y)
          mvars_loc
        @ [ (* SSP.AST.ProgramDefinition *)
            SSP.AST.Equations
              (* Questionmark *)
              ( pconcrete_ident f_name,
                pgeneric span generics
                @ List.map
                    ~f:(fun x ->
                      SSP.AST.Implicit
                        ( SSP.AST.Ident ("L" ^ Int.to_string x),
                          (SSP.AST.NameTy "{fset Location}" : SSP.AST.ty) ))
                    (List.init (List.length params) (fun x -> x + 1))
                @ List.map
                    ~f:(fun x ->
                      SSP.AST.Implicit
                        ( SSP.AST.Ident ("I" ^ Int.to_string x),
                          (SSP.AST.NameTy "Interface" : SSP.AST.ty) ))
                    (List.init (List.length params) (fun x -> x + 1))
                @ List.mapi
                    ~f:(fun i { pat; typ; typ_span; attrs } ->
                      SSP.AST.Explicit
                        ( ppat pat,
                          wrap_type_in_both
                            ("L" ^ Int.to_string (i + 1))
                            ("I" ^ Int.to_string (i + 1))
                            (pty span typ) ))
                    params,
                pexpr true body,
                wrap_type_in_both mvars_str ndep_str (pty span body.typ) );
          ]
        @ (List.concat_map ~f:(fun { kind; span } ->
            match kind with
            | Tool { path; tokens } when String.equal path "hax::init" ->
              let token_list = token_list tokens in
              let contract = strip_or_error ("contract argument missing") (get_argument "contract" token_list) e.span in
              [SSP.AST.Definition
                 ( "init_" ^ contract,
                   [],
                   SSP.AST.Var "st",
                   SSP.AST.TypeTy )]
            | Tool { path; tokens } when String.equal path "hax::receive" ->
              let token_list = token_list tokens in
              let contract = strip_or_error ("contract argument missing") (get_argument "contract" token_list) e.span in
              let name = strip_or_error ("name argument missing") (get_argument "name"  token_list) e.span in
              let parameter = get_argument "parameter"  token_list in
              let logger = get_argument "logger" token_list in
              let payable = get_argument "payable" token_list in
              [SSP.AST.Definition
                 ( "receive_" ^ contract ^ "_" ^ name,
                   List.map ~f:(fun x -> SSP.AST.Explicit (SSP.AST.Ident x, SSP.AST.WildTy))
                     (List.map ~f:strip (List.concat_map ~f:Option.to_list [parameter; logger; payable])) @
                   [SSP.AST.Explicit (SSP.AST.Ident "st", SSP.AST.NameTy ("state_" ^ contract))], (* Arguments *)
                   SSP.AST.App (SSP.AST.Var (pconcrete_ident f_name) (* contract *), [SSP.AST.Var "st"]),
                   SSP.AST.TypeTy )]
            | _ -> []
          ) e.attrs)
    | TyAlias { name; generics; ty } ->
        let g = pgeneric span generics in
        [
          (if List.is_empty g then
           SSP.AST.Notation (pconcrete_ident name, SSP.AST.Type (pty span ty))
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
        (*     ( pconcrete_ident name (\* ^ pconcrete_ident record_name *\), *)
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
                (SSP.AST.NameTy "{fset Location}" : SSP.AST.ty) );
            SSP.AST.Implicit
              (SSP.AST.Ident "I", (SSP.AST.NameTy "Interface" : SSP.AST.ty));
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
          SSP.AST.Equations
            ( "Build_" ^ U.Concrete_ident_view.to_definition_name name,
              implicit_LI
              @ pgeneric_implicit span generics
              @ List.map
                  ~f:(fun (x, y) ->
                    SSP.AST.Explicit
                      (SSP.AST.Ident x, wrap_type_in_both "L" "I" y))
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
                      [ SSP.AST.Var x; SSP.AST.Lambda ([ SSP.AST.Ident x ], z) ]
                    ))
                fields,
              SSP.AST.NameTy ("both L I" ^ " " ^ ty_name) )
          (* :: SSP.AST.Arguments ("Build_" ^ pconcrete_ident name,) *);
        ]
        @
        (List.concat_map ~f:(fun { kind; span } ->
             match kind with
         | Tool { path; tokens } when String.equal path "hax::contract_state" ->
           let token_list = token_list tokens in
           let contract = strip_or_error ("contract argument missing") (get_argument "contract" token_list) e.span in
           [SSP.AST.Definition
              ( "state_" ^ contract,
                [],
                SSP.AST.Var (pconcrete_ident name),
                SSP.AST.TypeTy )]
         | _ -> [])
            e.attrs
        )

    (* Definition t_Error : choice_type := t_ErrorKind × t_ErrorKind. *)
    (* (\* Uncurry is Build_.. fn *\) *)
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
        (*   (\* SSP.AST.Inductive *\) *)
        (*   (\*   ( U.Concrete_ident_view.to_definition_name name, *\) *)
        (*   (\*     pgeneric span generics, *\) *)
        (*   (\*     p_inductive span variants name ); *\) *)
        (* ] *)
        let number_of_cases = Int.to_string (List.length variants) in
        let implicit_LI =
          [
            SSP.AST.Implicit
              ( SSP.AST.Ident "L",
                (SSP.AST.NameTy "{fset Location}" : SSP.AST.ty) );
            SSP.AST.Implicit
              (SSP.AST.Ident "I", (SSP.AST.NameTy "Interface" : SSP.AST.ty));
          ]
        in
        SSP.AST.Definition
          ( "t_" ^ pconcrete_ident name,
            pgeneric span generics,
            SSP.AST.Type
              (SSP.AST.NameTy ("chFin (mkpos " ^ number_of_cases ^ ")")),
            SSP.AST.TypeTy )
        :: List.mapi variants
             ~f:(fun i { name = v_name; arguments; is_record } ->
               SSP.AST.Definition
                 ( pconcrete_ident v_name,
                   implicit_LI @ pgeneric span generics,
                   SSP.AST.Var
                     ("ret_both (fintype.Ordinal (n:=" ^ number_of_cases
                    ^ ") (m:=" ^ Int.to_string i ^ ") eq_refl : "
                    ^ pconcrete_ident name ^ ")"),
                   if is_record then
                     SSP.AST.NameTy ("both L I " ^ pconcrete_ident name)
                   else
                     match arguments with
                     | [] -> SSP.AST.NameTy ("both L I " ^ pconcrete_ident name)
                     | [ (arg_name, arg_ty, _arg_attrs) ] ->
                         SSP.AST.AppTy
                           ( pty span arg_ty,
                             [
                               SSP.AST.NameTy
                                 ("both L I " ^ pconcrete_ident name);
                             ] )
                     | _ ->
                         SSP.AST.Arrow
                           ( SSP.AST.Product
                               (List.map ~f:(snd3 >> pty span) arguments),
                             SSP.AST.NameTy ("both L I " ^ pconcrete_ident name)
                           ) ))
    | Type { name; generics; variants } ->
        let g = pgeneric span generics in
        [
          (if List.is_empty g then
           SSP.AST.Notation
             ( "t_" ^ pconcrete_ident name,
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
                    (SSP.AST.NameTy "{fset Location}" : SSP.AST.ty) );
                SSP.AST.Implicit
                  (SSP.AST.Ident "I", (SSP.AST.NameTy "Interface" : SSP.AST.ty));
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
                    ( "t_" ^ o.type_name,
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
                            (SSP.AST.NameTy "{fset Location}" : SSP.AST.ty) );
                        SSP.AST.Implicit
                          ( SSP.AST.Ident "I",
                            (SSP.AST.NameTy "Interface" : SSP.AST.ty) );
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
                    ( "t_" ^ o.bytes_name,
                      SSP.AST.Type
                        (SSP.AST.ArrayTy
                           ( SSP.AST.Int { size = SSP.AST.U8; signed = false },
                             (* int_of_string *) o.size )) );
                  SSP.AST.Definition
                    ( o.bytes_name,
                      [
                        SSP.AST.Implicit
                          ( SSP.AST.Ident "L",
                            (SSP.AST.NameTy "{fset Location}" : SSP.AST.ty) );
                        SSP.AST.Implicit
                          ( SSP.AST.Ident "I",
                            (SSP.AST.NameTy "Interface" : SSP.AST.ty) );
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
                  UnsignedPublicInteger.parse argument |> Result.ok_or_failwith
                in
                [
                  SSP.AST.Notation
                    ( "t_" ^ o.integer_name,
                      SSP.AST.Type
                        (SSP.AST.ArrayTy
                           ( SSP.AST.Int { size = SSP.AST.U8; signed = false },
                             Int.to_string ((o.bits + 7) / 8) )) );
                  SSP.AST.Definition
                    ( o.integer_name,
                      [
                        SSP.AST.Implicit
                          ( SSP.AST.Ident "L",
                            (SSP.AST.NameTy "{fset Location}" : SSP.AST.ty) );
                        SSP.AST.Implicit
                          ( SSP.AST.Ident "I",
                            (SSP.AST.NameTy "Interface" : SSP.AST.ty) );
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
                  SSP.AST.Notation ("t_" ^ o.bytes_name, SSP.AST.Type typ);
                  SSP.AST.Definition
                    ( o.bytes_name,
                      [
                        SSP.AST.Implicit
                          ( SSP.AST.Ident "L",
                            (SSP.AST.NameTy "{fset Location}" : SSP.AST.ty) );
                        SSP.AST.Implicit
                          ( SSP.AST.Ident "I",
                            (SSP.AST.NameTy "Interface" : SSP.AST.ty) );
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
                    ( "t_" ^ o.array_name,
                      SSP.AST.Type
                        (SSP.AST.ArrayTy
                           ( SSP.AST.Int { size = typ; signed = false },
                             (* int_of_string *) o.size )) );
                  SSP.AST.Definition
                    ( o.array_name,
                      [
                        SSP.AST.Implicit
                          ( SSP.AST.Ident "L",
                            (SSP.AST.NameTy "{fset Location}" : SSP.AST.ty) );
                        SSP.AST.Implicit
                          ( SSP.AST.Ident "I",
                            (SSP.AST.NameTy "Interface" : SSP.AST.ty) );
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
        else [ SSP.AST.Require ((* ns_crate:: ns_path @ *) path, rename) ]
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
                  | TIFn fn_ty ->
                    let loc_name = U.Concrete_ident_view.to_definition_name x.ti_ident ^ "_loc" in
                    let size, value =
                        wrap_type_in_enumerator
                          (fun (i : int) -> "L" ^ Int.to_string (i+1))
                          (fun (i : int) -> "I" ^ Int.to_string (i+1))
                          (pty x.ti_span fn_ty) [loc_name]
                      in
                      [ SSP.AST.Named (loc_name, SSP.AST.NameTy "{fset Location}");
                        SSP.AST.Named
                          ( U.Concrete_ident_view.to_definition_name x.ti_ident,
                            SSP.AST.Forall
                              ( List.map
                                  ~f:(fun (i : int) -> "L" ^ Int.to_string (i+1))
                                  (List.range 0 size)
                                @ List.map
                                    ~f:(fun (i : int) -> "I" ^ Int.to_string (i+1))
                                    (List.range 0 size),
                                [],
                                value ) );
                      ]
                  | TIType trait_refs ->
                      SSP.AST.Named ("t_" ^ U.Concrete_ident_view.to_definition_name x.ti_ident, SSP.AST.TypeTy)
                      :: List.map
                           ~f:(fun tr ->
                             SSP.AST.Coercion
                               ( "t_" ^ U.Concrete_ident_view.to_definition_name x.ti_ident ^ "_"
                                 ^ pconcrete_ident tr.trait,
                                 SSP.AST.AppTy
                                   ( SSP.AST.NameTy (pconcrete_ident tr.trait),
                                     [ SSP.AST.NameTy ("t_" ^ U.Concrete_ident_view.to_definition_name x.ti_ident) ] ) ))
                           trait_refs
                  (* (match List.rev trait_refs with *)
                  (* | _ :: xs -> List.rev xs *)
                  (* | _ -> []) *))
                items );
        ]

    | Impl { generics; self_ty; of_trait = name, gen_vals; items } ->
      let mvars_locs =
        List.map ~f:(fun x ->
               let (mvars_ext, mvars_loc)
                 : local_ident list * (local_ident * AST.ty * int) list =
                 match
                   Map.find
                     (ctx.analysis_data.mut_var
                      : (local_ident list * ((local_ident * AST.ty) * int) list)
                          Map.M(Concrete_ident).t)
                     x.ii_ident
                 with
                 | Some l ->
                   ( fst l,
                     List.map ~f:(fun ((x, x_ty), x_n) -> (x, x_ty, x_n)) (snd l) )
                 | None -> ([], [])
               in
               mvars_loc)
          items
      in
      (* [SSP.AST.Unimplemented (Map.fold ~init:"" ~f:(fun ~key:k ~data:d x -> x ^ " " ^ pconcrete_ident k (\* ^ " " ^ d *\)) ctx.analysis_data.mut_var)] @ *)
      (* [SSP.AST.Unimplemented (Map.fold ~init:"" ~f:(fun ~key:k ~data:d x -> x ^ " " ^ pconcrete_ident k (\* ^ " " ^ d *\)) (fst ctx.analysis_data.func_dep))] @ *)
      List.concat_map
                ~f:(fun x ->
                    let (mvars_loc) =
                      match
                        Map.find
                          (fst ctx.analysis_data.func_dep)
                          x.ii_ident
                      with
                      | Some l -> l
                      | None -> []
                    in
                    let mvars_loc_fset_str = "fset" ^ " " ^ "[" ^ String.concat ~sep:";" (List.map ~f:pconcrete_ident mvars_loc) ^ "]" in
                    (if List.length mvars_loc > 0
                     then [SSP.AST.Unimplemented (U.Concrete_ident_view.to_definition_name x.ii_ident ^ " " ^ mvars_loc_fset_str)]
                     else [])
          ) items @
      [SSP.AST.Unimplemented ("SEPERATOR")] @
      List.concat_map
                ~f:(fun x ->
                    let (mvars_ext, mvars_loc)
                      : local_ident list * (local_ident * AST.ty * int) list =
                      match
                        Map.find
                          (ctx.analysis_data.mut_var
                           : (local_ident list * ((local_ident * AST.ty) * int) list)
                               Map.M(Concrete_ident).t)
                          x.ii_ident
                      with
                      | Some l -> ( fst l, List.map ~f:(fun ((x, x_ty), x_n) -> (x, x_ty, x_n)) (snd l) )
                      | None -> ([], [])
                    in
                    let mvars_loc_fset_str = "fset" ^ " " ^ "[" ^ String.concat ~sep:";" (List.map ~f:(fun (x,x_ty,x_n) -> x.name ^ "_loc") mvars_loc) ^ "]" in
                    (if List.length mvars_loc > 0
                     then [SSP.AST.Unimplemented (U.Concrete_ident_view.to_definition_name x.ii_ident ^ " " ^ mvars_loc_fset_str)]
                     else [])
          ) items @
      (List.fold_left ~init:[]
         ~f:(fun y (x, x_ty, x_n) ->
             SSP.AST.Definition
               ( x.name ^ "_loc",
                 pgeneric_implicit span generics,
                 SSP.AST.Const
                   (SSP.AST.Const_string
                      ("("
                       ^ SSP.ty_to_string (pty (Span.dummy ()) x_ty)
                       ^ " ; " ^ Int.to_string x_n ^ "%nat)")),
                 SSP.AST.NameTy "Location" )
             :: y)
         (List.concat mvars_locs))
      @ [
          SSP.AST.ProgramInstance
            ( pglobal_ident name,
              pgeneric span generics,
              pty span self_ty,
              args_ty span gen_vals,
              List.concat_map
                ~f:(fun x ->
                    let (mvars_ext, mvars_loc)
                      : local_ident list * (local_ident * AST.ty * int) list =
                      match
                        Map.find
                          (ctx.analysis_data.mut_var
                           : (local_ident list * ((local_ident * AST.ty) * int) list)
                               Map.M(Concrete_ident).t)
                          x.ii_ident
                      with
                      | Some l -> ( fst l, List.map ~f:(fun ((x, x_ty), x_n) -> (x, x_ty, x_n)) (snd l) )
                      | None -> ([], [])
                    in
                    let mvars_loc_fset_str = "fset" ^ " " ^ "[" ^ String.concat ~sep:";" (List.map ~f:(fun (x,x_ty,x_n) -> x.name ^ "_loc") mvars_loc) ^ "]" in
                    match x.ii_v with
                    | IIFn { body; params } ->
                      [SSP.AST.InlineDef
                         (U.Concrete_ident_view.to_definition_name x.ii_ident ^ "_loc",
                          [],
                          SSP.AST.NameTerm mvars_loc_fset_str,
                          SSP.AST.NameTy "{fset Location}");
                       SSP.AST.LetDef
                         ( U.Concrete_ident_view.to_definition_name x.ii_ident,
                           (if List.is_empty params
                            then [SSP.AST.Implicit
                                    ( SSP.AST.Ident ("L"),
                                      (SSP.AST.NameTy "{fset Location}" : SSP.AST.ty) ) ;
                                  SSP.AST.Implicit
                                    ( SSP.AST.Ident ("I"),
                                      (SSP.AST.NameTy "Interface" : SSP.AST.ty) )]
                            else
                              List.map
                                ~f:(fun x ->
                                    SSP.AST.Implicit
                                      ( SSP.AST.Ident ("L" ^ Int.to_string x),
                                        (SSP.AST.NameTy "{fset Location}" : SSP.AST.ty) ))
                                (List.init (List.length params) (fun x -> x + 1))
                              @ List.map
                                ~f:(fun x ->
                                    SSP.AST.Implicit
                                      ( SSP.AST.Ident ("I" ^ Int.to_string x),
                                        (SSP.AST.NameTy "Interface" : SSP.AST.ty) ))
                                (List.init (List.length params) (fun x -> x + 1))
                              @ List.mapi
                                ~f:(fun i { pat; typ; typ_span; attrs } ->
                                    SSP.AST.Explicit
                                      ( ppat pat,
                                        wrap_type_in_both
                                          ("L" ^ Int.to_string (i + 1))
                                          ("I" ^ Int.to_string (i + 1))
                                          (pty span typ) ))
                                params),
                           pexpr true body,
                           let lis, iis =
                             if List.length params == 0
                             then ["L"], ["I"]
                             else List.unzip (List.map ~f:(fun i -> (("L" ^ Int.to_string (i + 1)), ("I" ^ Int.to_string (i + 1)))) (List.range 0 (List.length params)))
                           in
                           let lis = lis @ (if List.length mvars_loc > 0 then [mvars_loc_fset_str] else []) in
                           let iis = iis in
                           wrap_type_in_both
                             (let lis_str = String.concat ~sep:" :|: " lis in
                              if List.length lis <= 1 then lis_str else "(" ^ lis_str ^ ")")
                             (let iis_str = String.concat ~sep:" :|: " iis in
                              if List.length iis <= 1 then iis_str else "(" ^ iis_str ^ ")")
                             (pty span body.typ) )]
                    | IIType ty ->
                      [SSP.AST.LetDef ( "t_" ^ U.Concrete_ident_view.to_definition_name x.ii_ident,
                        [],
                        SSP.AST.Type (pty span ty),
                        SSP.AST.TypeTy )])
                items );
        ]
    in
    decls_from_attr @ decls_from_item

  and p_inductive span variants parrent_name : SSP.AST.inductive_case list =
    List.map variants ~f:(fun { name; arguments; is_record } ->
        if is_record then
          SSP.AST.InductiveCase
            ( U.Concrete_ident_view.to_definition_name name,
              SSP.AST.RecordTy
                (pconcrete_ident name, p_record_record span arguments) )
        else
          let name = U.Concrete_ident_view.to_definition_name name in
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
end

let make ctx =
  (module Make (struct
    let ctx = ctx
  end) : S)

let string_of_item (analysis_data : StaticAnalysis.analysis_data) (item : item)
    : string =
  let (module Print) =
    make
      {
        current_namespace = U.Concrete_ident_view.to_namespace item.ident;
        analysis_data;
      }
  in
  List.map ~f:SSP.decl_to_string @@ Print.pitem item |> String.concat ~sep:"\n"

let string_of_items =
  (fun (x, y) -> List.map ~f:(string_of_item y) x)
  >> List.map ~f:String.strip
  >> List.filter ~f:(String.is_empty >> not)
  >> String.concat ~sep:"\n\n"

let hardcoded_coq_headers =
  "(* File automatically generated by Hacspec *)\n\
   Set Warnings \"-notation-overridden,-ambiguous-paths\".\n\
   From Crypt Require Import choice_type Package Prelude.\n\
   Import PackageNotation.\n\
   From extructures Require Import ord fset.\n\
   From mathcomp Require Import ssrZ word.\n\
   From Jasmin Require Import word.\n\n\
   From Coq Require Import ZArith.\n\
   From Coq Require Import Strings.String.\n\
  \   Import List.ListNotations.\n\
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
   Obligation Tactic := (* try timeout 8 *) solve_ssprove_obligations.\n\
   Require Import Core.\n\
   Require Import Hacspec_lib.\n"

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
               ^ string_of_items (items, analysis_data) ^ "\n"
               ^ SSP.decl_to_string (SSP.AST.Inductive (
                   "Msg",
                   [],
                   List.filter_map ~f:(function
                       | { kind = Tool { path; tokens }; span } when String.equal path "hax::receive" ->
                         let token_list = token_list tokens in
                         let name = strip_or_error ("name argument missing") (get_argument "name"  token_list) (Span.dummy ()) in
                         Some (SSP.AST.BaseCase name)
                       | _ -> None)
                     (List.concat_map ~f:(fun x -> x.attrs) items)))
               ^ "\n";
           })

let apply_phases (bo : BackendOptions.t) (i : Ast.Rust.item list) :
    AST.item list =
  TransformToInputLanguage.ditems i

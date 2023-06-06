open Hax_engine
open Utils
open Base

include
  Backend.Make
    (struct
      open Features
      include Off
      include On.Slice
      include On.Monadic_binding
      include On.Macro
    end)
    (struct
      let backend = Diagnostics.Backend.Coq
    end)

module RejectNotCoq (FA : Features.T) = struct
  module FB = InputLanguage

  include
    Feature_gate.Make (FA) (FB)
      (struct
        module A = FA
        module B = FB
        include Feature_gate.DefaultSubtype

        let mutable_variable = reject
        let loop = reject
        let continue = reject
        let mutable_reference = reject
        let mutable_pointer = reject
        let mutable_borrow = reject
        let reference = reject
        let slice _ = Features.On.slice
        let raw_pointer = reject
        let early_exit _ = Obj.magic ()
        let question_mark = reject
        let macro _ = Features.On.macro
        let as_pattern = reject
        let lifetime = reject
        let monadic_action = reject
        let arbitrary_lhs = reject
        let nontrivial_lhs = reject
        let monadic_binding _ = Features.On.monadic_binding
        let state_passing_loop = reject
        let for_loop = reject

        let metadata =
          Phase_utils.Metadata.make (Reject (NotInBackendLang backend))
      end)
end

module AST = Ast.Make (InputLanguage)
module BackendOptions = Backend.UnitBackendOptions
open Ast
module U = Ast_utils.Make (InputLanguage)
open AST

(* Helpers for constructing an Coq surface AST *)
module C = struct
  (* module AST = FStar_Parser_AST (\* https://ocaml.org/p/fstar/2022.01.15/doc/FStar_Parser_AST/index.html *\) *)
  module AST = struct
    type int_size = U8 | U16 | U32 | U64 | U128
    type int_type = int_size * bool

    type ty =
      | Wild
      | Bool
      | Unit
      | Int of int_type
      | Name of string
      | RecordTy of string * (string * ty) list
      | Product of ty list
      | Arrow of ty * ty
      | ArrayTy of ty * string (* int *)
      | SliceTy of ty
      | AppTy of string * ty list
      | NatMod of string * int * string

    type literal =
      | Const_string of string
      | Const_char of int
      | Const_int of string * int_type
      | Const_bool of bool

    type pat =
      | Wild
      | UnitPat
      | Ident of string
      | Lit of literal
      | RecordPat of string * (string * pat) list
      | TuplePat of pat list
      | AscriptionPat of pat * ty

    type term =
      | UnitTerm
      | Let of pat * term * term * ty
      | If of term * term * term
      | Match of term * (pat * term) list
      | Const of literal
      | Literal of string
      | AppFormat of string list * term list
      | App of term * term list
      | Var of string
      | Name of string
      | RecordConstructor of term * (string * term) list
      | Type of ty
      | Lambda of pat list * term
      | Tuple of term list
      | Array of term list

    type inductive_case = InductiveCase of string * ty | BaseCase of string
    type definition_type = string * (pat * ty) list * term * ty
    type generics_type = string list

    type decl =
      | Unimplemented of string
      | Definition of definition_type
      | Notation of string * ty
      | Record of string * (string * ty) list
      | Inductive of string * generics_type * inductive_case list
      | Class of string * (string * ty) list * generics_type
      | Instance of string * ty * ty list * definition_type list
      | Require of string list * string option
  end
end

module Context = struct
  type t = { current_namespace : string * string list }
end

let tabsize = 2
let newline_indent depth : string = "\n" ^ String.make (tabsize * depth) ' '

let int_size_to_string (x : C.AST.int_size) : string =
  match x with
  | C.AST.U8 -> "8"
  | C.AST.U16 -> "16"
  | C.AST.U32 -> "32"
  | C.AST.U64 -> "64"
  | C.AST.U128 -> "128"
  | _ -> .

let rec ty_to_string (x : C.AST.ty) : C.AST.decl list * string =
  match x with
  | C.AST.Wild -> ([], "_")
  | C.AST.Bool -> ([], "bool")
  | C.AST.Unit -> ([], "unit")
  | C.AST.Int (int_size, true) -> ([], "int" ^ int_size_to_string int_size)
  | C.AST.Int (int_size, false) -> ([], "int" ^ int_size_to_string int_size)
  | C.AST.Name s -> ([], s)
  | C.AST.RecordTy (name, fields) -> ([ C.AST.Record (name, fields) ], name)
  | C.AST.Product l ->
      let p_decl, p_str = product_to_string l (" " ^ "'×" ^ " ") in
      (p_decl, "(" ^ p_str ^ ")")
  | C.AST.Arrow (a, b) ->
      let a_ty_def, a_ty_str = ty_to_string a in
      let b_ty_def, b_ty_str = ty_to_string b in
      (a_ty_def @ b_ty_def, a_ty_str ^ " " ^ "->" ^ " " ^ b_ty_str)
  | C.AST.ArrayTy (t, l) ->
      let ty_def, ty_str = ty_to_string t in
      (ty_def, "nseq" ^ " " ^ ty_str ^ " " ^ (* Int.to_string *) l)
  | C.AST.SliceTy t ->
      let ty_def, ty_str = ty_to_string t in
      (ty_def, "seq" ^ " " ^ ty_str)
  | C.AST.AppTy (i, []) -> ([], i)
  | C.AST.AppTy (i, [ y ]) ->
      let ty_defs, ty_str = ty_to_string y in
      (ty_defs, i ^ " " ^ ty_str)
  | C.AST.AppTy (i, p) ->
      let ty_def, ty_str = product_to_string p ") (" in
      (ty_def, i ^ " " ^ "(" ^ ty_str ^ ")")
  | C.AST.NatMod (t, i, s) ->
      ( [
          C.AST.Notation
            (t, C.AST.ArrayTy (C.AST.Int (U8, false), Int.to_string i));
        ],
        "nat_mod 0x" ^ s )
  | _ -> .

and product_to_string (x : C.AST.ty list) (sep : string) :
    C.AST.decl list * string =
  match x with
  | [ y ] -> ty_to_string y
  | y :: ys ->
      let ty_defs, ty_str = ty_to_string y in
      let ys_defs, ys_str = product_to_string ys sep in
      (ty_defs @ ys_defs, ty_str ^ sep ^ ys_str)
  | [] -> ([], "")
(* and record_fields_to_string (x : (string * C.AST.ty) list) : C.AST.decl list * string = *)
(*   match x with *)
(*   | (name, ty) :: xs -> *)
(*      let ty_def, ty_str = ty_to_string ty in *)
(*      let xs_def, xs_str = record_fields_to_string xs in *)
(*      ty_def @ xs_def, newline_indent 1 ^ name ^ ":" ^ " " ^ ty_str ^ ";" ^ xs_str *)
(*   | _ -> [], "" *)

let literal_to_string (x : C.AST.literal) : string =
  match x with
  | Const_string s -> s
  | Const_char c -> Int.to_string c (* TODO *)
  | Const_int (i, (int_size, b)) ->
      "(@repr" ^ " " ^ "WORDSIZE" ^ int_size_to_string int_size ^ " " ^ i ^ ")"
  | Const_bool b -> Bool.to_string b

let rec pat_to_string (x : C.AST.pat) (is_top_expr : bool) depth : string =
  match x with
  | C.AST.Wild -> "_"
  | C.AST.UnitPat -> tick_if is_top_expr ^ "tt"
  | C.AST.Ident s -> s
  | C.AST.Lit l -> literal_to_string l
  | C.AST.RecordPat (name, args) ->
      (* name ^ " " ^ *)
      "{|" ^ record_pat_to_string args (depth + 1) ^ newline_indent depth ^ "|}"
  | C.AST.TuplePat vals ->
      tick_if is_top_expr ^ "(" ^ tuple_pat_to_string vals (depth + 1) ^ ")"
  | C.AST.AscriptionPat (p, ty) ->
      pat_to_string p true depth (* TODO: Should this be true of false? *)

and tick_if is_top_expr = if is_top_expr then "'" else ""

and tuple_pat_to_string vals depth =
  match vals with
  | [ t ] -> pat_to_string t false depth
  | t :: ts -> pat_to_string t false depth ^ "," ^ tuple_pat_to_string ts depth
  | [] -> "todo empty tuple pattern?"

and record_pat_to_string args depth : string =
  match args with
  | (name, pat) :: xs ->
      newline_indent depth ^ name ^ " " ^ ":=" ^ " "
      ^ pat_to_string pat true depth
      ^ ";"
      ^ record_pat_to_string xs depth
  | _ -> ""

let rec term_to_string (x : C.AST.term) depth : string * bool =
  match x with
  | C.AST.UnitTerm -> ("tt", false)
  | C.AST.Let (pat, bind, term, typ) ->
      let _, ty_str = ty_to_string typ in
      (* TODO: propegate type definition *)
      ( "let" ^ " "
        ^ pat_to_string pat true depth
        ^ " " ^ ":=" ^ " "
        ^ term_to_string_without_paren bind (depth + 1)
        ^ " " ^ ":" ^ " " ^ ty_str ^ " " ^ "in" ^ newline_indent depth
        ^ term_to_string_without_paren term depth,
        true )
  | C.AST.If (cond, then_, else_) ->
      ( "if"
        ^ newline_indent (depth + 1)
        ^ term_to_string_without_paren cond (depth + 1)
        ^ newline_indent depth ^ "then"
        ^ newline_indent (depth + 1)
        ^ term_to_string_without_paren then_ (depth + 1)
        ^ newline_indent depth ^ "else"
        ^ newline_indent (depth + 1)
        ^ term_to_string_without_paren else_ (depth + 1),
        true )
  | C.AST.Match (match_val, arms) ->
      ( "match" ^ " "
        ^ term_to_string_without_paren match_val (depth + 1)
        ^ " " ^ "with" ^ newline_indent depth ^ arm_to_string arms depth ^ "end",
        false )
  | C.AST.Const c -> (literal_to_string c, false)
  | C.AST.Literal s -> (s, false)
  | C.AST.AppFormat (format, args) ->
      ( format_to_string format
          (List.map ~f:(fun x -> term_to_string_with_paren x depth) args),
        true (* TODO? Notation does not always need paren *) )
  | C.AST.App (f, args) ->
      let f_s, f_b = term_to_string f depth in
      (f_s ^ args_to_string args depth, f_b || List.length args > 0)
  | C.AST.Var s -> (s, false)
  | C.AST.Name s -> (s, false)
  | C.AST.RecordConstructor (f, args) ->
      ( "Build_"
        ^ term_to_string_without_paren f depth
        ^ " "
        ^ record_args_to_string args depth,
        true )
  | C.AST.Type t ->
      let _, ty_str = ty_to_string t in
      (* TODO: Make definitions? *)
      (ty_str, true (* TODO? does this always need paren? *))
  | C.AST.Lambda (params, body) ->
      ( "fun"
        ^ lambda_params_to_string params depth
        ^ " " ^ "=>"
        ^ newline_indent (depth + 1)
        ^ term_to_string_without_paren body (depth + 1),
        true )
  | C.AST.Tuple vals ->
      ("(" ^ tuple_term_to_string vals (depth + 1) ^ ")", false)
      (* List.fold_left ~init:(term_to_string_without_paren t (depth+1)) ~f:(fun x y -> "(" ^ x ^ "," ^ term_to_string_without_paren y (depth+1) ^ ")") ts, false *)
  | C.AST.Array (t :: ts) ->
      ( "array_from_list" ^ " " ^ "_" ^ " " ^ "["
        ^ List.fold_left
            ~init:(term_to_string_without_paren t (depth + 1))
            ~f:(fun x y -> x ^ ";" ^ term_to_string_without_paren y (depth + 1))
            ts
        ^ "]",
        true )
  | C.AST.Array [] -> ("!TODO empty array!", false)
  | _ -> .

and tuple_term_to_string vals depth : string =
  match vals with
  | [ t ] -> term_to_string_without_paren t depth
  | t :: ts ->
      term_to_string_without_paren t depth ^ "," ^ tuple_term_to_string ts depth
  | [] -> "!TODO empty tuple!"

and lambda_params_to_string (params : C.AST.pat list) depth : string =
  match params with
  | x :: xs ->
      " " ^ pat_to_string x true depth ^ lambda_params_to_string xs depth
  | [] -> ""

and term_to_string_with_paren (x : C.AST.term) depth : string =
  let s, b = term_to_string x depth in
  if b then "(" ^ s ^ ")" else s

and term_to_string_without_paren (x : C.AST.term) depth : string =
  let s, _ = term_to_string x depth in
  s

and format_to_string (format : string list) (args : string list) : string =
  match format with
  | f :: fs -> (
      match args with x :: xs -> f ^ x ^ format_to_string fs xs | [] -> f)
  | [] -> failwith "incorrect formatting"

and record_args_to_string (args : (string * C.AST.term) list) depth : string =
  match args with
  | (i, t) :: xs ->
      term_to_string_with_paren t depth ^ record_args_to_string xs depth
  | _ -> ""

and args_to_string (args : C.AST.term list) depth : string =
  match args with
  | x :: xs -> " " ^ term_to_string_with_paren x depth ^ args_to_string xs depth
  | _ -> ""

and arm_to_string (x : (C.AST.pat * C.AST.term) list) depth : string =
  match x with
  | (pat, body) :: xs ->
      "|" ^ " "
      ^ pat_to_string pat true depth
      ^ " " ^ "=>" ^ " "
      ^ term_to_string_without_paren body (depth + 1)
      ^ newline_indent depth ^ arm_to_string xs depth
  | _ -> ""

let rec decl_to_string (x : C.AST.decl) : string =
  match x with
  | C.AST.Unimplemented s -> "(*" ^ s ^ "*)"
  | C.AST.Definition (name, params, term, ty) ->
      let definitions, ty_str = ty_to_string ty in
      decl_list_to_string definitions
      ^ "Definition" ^ " " ^ name ^ " " ^ params_to_string params ^ ":" ^ " "
      ^ ty_str ^ " " ^ ":=" ^ newline_indent 1
      ^ term_to_string_without_paren term 1
      ^ "."
  | C.AST.Notation (name, ty) ->
      let definitions, ty_str = ty_to_string ty in
      decl_list_to_string definitions
      ^ "Notation" ^ " " ^ name ^ " " ^ ":=" ^ " " ^ "(" ^ ty_str ^ ")" ^ "."
  | C.AST.Record (name, variants) ->
      let definitions, variants_str =
        variants_to_string variants (newline_indent 1) ";"
      in
      decl_list_to_string definitions
      ^ "Record" ^ " " ^ name ^ " " ^ ":" ^ " " ^ "Type" ^ " " ^ ":=" ^ "{"
      ^ variants_str ^ newline_indent 0 ^ "}."
  | C.AST.Inductive (name, generics, variants) ->
      let name_generics =
        name ^ List.fold_left ~init:"" ~f:(fun a b -> a ^ " " ^ b) generics
      in
      let definitions, variants_str =
        inductive_case_to_string variants
          (newline_indent 0 ^ "|" ^ " ")
          name_generics
      in
      let _, args_str =
        if List.length generics == 0 then ([], "")
        else
          inductive_case_args_to_string variants
            (newline_indent 0 ^ "Arguments" ^ " ")
            (List.fold_left ~init:"" ~f:(fun a b -> a ^ " {_}") generics)
            "."
      in
      decl_list_to_string definitions
      ^ "Inductive" ^ " " ^ name_generics ^ " " ^ ":" ^ " " ^ "Type" ^ " "
      ^ ":=" ^ variants_str ^ "." ^ args_str
  | C.AST.Class (name, trait_items, generics) ->
      let field_defs, field_str =
        List.fold_left ~init:([], "")
          ~f:(fun x y ->
            let definitions, ty_str = ty_to_string (snd y) in
            ( definitions @ fst x,
              snd x ^ newline_indent 1 ^ fst y ^ ":" ^ ty_str ^ " " ^ ";" ))
          trait_items
      in
      let name_generics =
        name ^ List.fold_left ~init:"" ~f:(fun a b -> a ^ " " ^ b) generics
      in
      decl_list_to_string field_defs
      ^ "Class" ^ " " ^ name_generics ^ " " ^ ":=" ^ " " ^ "{" ^ field_str
      ^ newline_indent 0 ^ "}" ^ "."
  | C.AST.Instance (name, self_ty, ty_list, impl_list) ->
      let ty_list_defs, ty_list_str =
        List.fold_left ~init:([], "")
          ~f:(fun x y ->
            let definitions, ty_str = ty_to_string y in
            (definitions @ fst x, snd x ^ ty_str ^ " "))
          ty_list
      in
      let impl_str =
        List.fold_left ~init:""
          ~f:(fun x y ->
            let name, params, term, ty = y in
            x ^ newline_indent 1 ^ name ^ " " ^ params_to_string params ^ ":="
            ^ " "
            ^ term_to_string_without_paren term 1
            ^ ";")
          impl_list
      in
      let ty_defs, ty_str = ty_to_string self_ty in
      decl_list_to_string (ty_list_defs @ ty_defs)
      ^ "Instance" ^ " " ^ ty_str ^ "_" ^ name ^ " " ^ ":" ^ " " ^ name ^ " "
      ^ ty_list_str ^ ":=" ^ " " ^ "{" ^ impl_str ^ newline_indent 0 ^ "}" ^ "."
  | C.AST.Require ([], rename) -> ""
  | C.AST.Require (import :: imports, rename) -> (
      "Require Import" ^ " "
      ^ map_first_letter String.uppercase import
        (* (List.fold_left ~init:import ~f:(fun x y -> x ^ "." ^ y) imports) *)
      ^ "."
      ^ match rename with Some s -> " (* " ^ "as " ^ s ^ " *)" | _ -> "")

and decl_list_to_string (x : C.AST.decl list) : string =
  List.fold_right ~init:""
    ~f:(fun x y -> decl_to_string x ^ newline_indent 0 ^ y)
    x

and params_to_string params : string =
  match params with
  | (pat, ty) :: xs ->
      let _, ty_str = ty_to_string ty in
      "(" ^ pat_to_string pat true 0 ^ " " ^ ":" ^ " " ^ ty_str ^ ")" ^ " "
      ^ params_to_string xs (* TODO: Should pat_to_string have tick here? *)
  | [] -> ""

and inductive_case_to_string variants pre post : C.AST.decl list * string =
  match variants with
  | x :: xs ->
      let ty_def, mid_str =
        match x with
        | C.AST.BaseCase ty_name -> ([], ty_name)
        | C.AST.InductiveCase (ty_name, ty) ->
            let ty_definitions, ty_str = ty_to_string ty in
            ( ty_definitions,
              ty_name ^ " " ^ ":" ^ " " ^ ty_str ^ " " ^ "->" ^ " " )
      in
      let variant_definitions, variants_str =
        inductive_case_to_string xs pre post
      in
      (ty_def @ variant_definitions, pre ^ mid_str ^ post ^ variants_str)
  | [] -> ([], "")

and inductive_case_args_to_string variants pre mid post :
    C.AST.decl list * string =
  List.fold_left ~init:([], "")
    ~f:(fun y x ->
      let mid_str, ty_str =
        match x with
        | C.AST.BaseCase ty_name -> (ty_name, "")
        | C.AST.InductiveCase (ty_name, ty) ->
            let _, ty_str = ty_to_string ty in
            (ty_name, " " ^ ty_str)
      in
      match y with
      | variant_definitions, variants_str ->
          ( variant_definitions,
            pre ^ mid_str ^ mid ^ ty_str ^ post ^ variants_str ))
    variants

and variants_to_string variants pre post : C.AST.decl list * string =
  List.fold_left ~init:([], "")
    ~f:(fun (variant_definitions, variants_str) (ty_name, ty) ->
      let ty_definitions, ty_str = ty_to_string ty in
      ( ty_definitions @ variant_definitions,
        pre ^ ty_name ^ " " ^ ":" ^ " " ^ ty_str ^ post ^ variants_str ))
    variants

let primitive_to_string (id : primitive_ident) : string =
  match id with
  | Box -> "(TODO: BOX)" (* failwith "Box" *)
  | Deref -> "(TODO: Deref)" (* failwith "Deref" *)
  | Cast -> "(TODO: Cast)" (* failwith "Cast" *)
  | BinOp op -> (
      match op with
      | Add -> "MachineIntegers.add"
      | Sub -> "MachineIntegers.sub"
      | Mul -> "MachineIntegers.mul"
      | Div -> "MachineIntegers.divs"
      | Eq -> "eq_op"
      | Lt -> "lt_op"
      | Le -> "le_op"
      | Ge -> "ge_op"
      | Gt -> "gt_op"
      | Ne -> "ne_op"
      | Rem -> "MachineIntegers.mods" (* .% *)
      | BitXor -> "MachineIntegers.xor" (* .^ *)
      | BitAnd -> "MachineIntegers.and" (* .& *)
      | BitOr -> "MachineIntegers.or" (* .| *)
      | Shl -> "shift_left_" (* shift_left *)
      | Shr -> "shift_right_" (* shift_right *)
      | Offset -> "(TODO: Offset)" (* failwith "TODO: Offset" *))
  | UnOp op -> "(TODO: UnOp)"
  | LogicalOp op -> ( match op with And -> "andb" | Or -> "orb")

module Make (Ctx : sig
  val ctx : Context.t
end) =
struct
  open Ctx

  let pconcrete_ident (id : concrete_ident) : string =
    let id_path = Non_empty_list.to_list id.path in
    let crate, path = ctx.current_namespace in
    if
      String.(crate = id.crate)
      && [%eq: string list] (List.drop_last_exn id_path) path
    then List.last_exn id_path
    else
      (* id.crate ^ "_" ^ *)
      (* List.fold_left ~init:"" ~f:(fun x y -> x ^ "_" ^ y) *)
      List.last_exn id_path

  let pglobal_ident (id : global_ident) : string =
    match id with
    | `Projector (`Concrete cid) | `Concrete cid -> pconcrete_ident cid
    | `Primitive p_id -> primitive_to_string p_id
    | `TupleType i -> "TODO (global ident) tuple type"
    | `TupleCons i -> "TODO (global ident) tuple cons"
    | `Projector (`TupleField (i, j)) | `TupleField (i, j) ->
        "TODO (global ident) tuple field"
    | _ -> .

  let pglobal_ident_last (id : global_ident) : string =
    match id with
    | `Concrete { crate; path } -> Non_empty_list.last path
    | `Primitive p_id -> "TODO (global ident last) primitive"
    | `TupleType i -> "TODO (global ident last) tuple type"
    | `TupleCons i -> "TODO (global ident last) tuple cons"
    | `TupleField i -> "TODO (global ident last) tuple field"
    | `Projector (`Concrete cid) -> "TODO (global ident last) projector cid"
    | `Projector (`TupleField (i, j)) ->
        "TODO (global ident last) projector tuplefield"
    | _ -> .

  module TODOs_debug = struct
    let __TODO_pat__ _ s = C.AST.Ident (s ^ " todo(pat)")
    let __TODO_ty__ _ s : C.AST.ty = C.AST.Name (s ^ " todo(ty)")
    let __TODO_item__ _ s = C.AST.Unimplemented (s ^ " todo(item)")
    let __TODO_term__ _ s = C.AST.Const (C.AST.Const_string (s ^ " todo(term)"))
  end

  module TODOs = struct
    let __TODO_ty__ span s : C.AST.ty =
      Error.unimplemented ~details:("[ty] node " ^ s) span

    let __TODO_pat__ span s =
      Error.unimplemented ~details:("[pat] node " ^ s) span

    let __TODO_term__ span s =
      Error.unimplemented ~details:("[expr] node " ^ s) span

    let __TODO_item__ span s = C.AST.Unimplemented (s ^ " todo(item)")
  end

  open TODOs

  let pint_kind (k : int_kind) : C.AST.int_type =
    ( (match k.size with
      | S8 -> U8
      | S16 -> U16
      | S32 -> U32
      | S64 -> U64
      | S128 -> U128
      | SSize -> U32),
      k.signedness == Signed )

  let rec pliteral (e : literal) =
    match e with
    | String s -> C.AST.Const_string s
    | Char c -> C.AST.Const_char (Char.to_int c)
    | Int { value; kind } -> C.AST.Const_int (value, pint_kind kind)
    | Float _ -> failwith "Float: todo"
    | Bool b -> C.AST.Const_bool b

  let rec pty span (t : ty) : C.AST.ty =
    match t with
    | TBool -> C.AST.Bool
    | TChar -> __TODO_ty__ span "char"
    | TInt k -> C.AST.Int (pint_kind k)
    | TStr -> __TODO_ty__ span "str"
    | TFalse -> __TODO_ty__ span "false"
    | TApp { ident = `TupleType 0 as ident; args = [] } -> C.AST.Unit
    | TApp { ident = `TupleType 1; args = [ GType ty ] } -> pty span ty
    | TApp { ident = `TupleType n; args } when n >= 2 ->
        C.AST.Product (args_ty span args)
    | TApp { ident; args } ->
        C.AST.AppTy (pglobal_ident ident ^ "_t", args_ty span args)
    | TArrow (inputs, output) ->
        List.fold_right ~init:(pty span output)
          ~f:(fun x y -> C.AST.Arrow (x, y))
          (List.map ~f:(pty span) inputs)
    | TFloat -> failwith "pty: Float"
    | TArray { typ; length } ->
        C.AST.ArrayTy (pty span typ, Int.to_string length)
    | TSlice { ty; _ } -> C.AST.SliceTy (pty span ty)
    | TParam i -> C.AST.Name i.name
    | TProjectedAssociatedType s ->
        C.AST.Wild
        (* __TODO_ty__ span ("proj:assoc:type" ^ s) *)
        (* failwith "proj:assoc:type" *)
    | _ -> .

  and args_ty span (args : generic_value list) : C.AST.ty list =
    (* List.map ~f:pty *)
    match args with
    | arg :: xs ->
        (match arg with
        | GLifetime { lt; witness } -> __TODO_ty__ span "lifetime"
        | GType x -> pty span x
        | GConst _ -> __TODO_ty__ span "const")
        :: args_ty span xs
    | [] -> []

  let rec ppat (p : pat) : C.AST.pat =
    match p.p with
    | PWild -> C.AST.Wild
    | PAscription { typ; pat } -> C.AST.AscriptionPat (ppat pat, pty p.span typ)
    | PBinding
        {
          mut = Immutable;
          mode = _;
          subpat = None;
          var;
          typ = _ (* we skip type annot here *);
        } ->
        C.AST.Ident var.name
    | PArray { args } -> __TODO_pat__ p.span "Parray?"
    | PConstruct { name = `TupleCons 0; args = [] } -> C.AST.UnitPat
    | PConstruct { name = `TupleCons 1; args = [ { pat } ] } ->
        __TODO_pat__ p.span "tuple 1"
    | PConstruct { name = `TupleCons n; args } ->
        C.AST.TuplePat (List.map ~f:(fun { pat } -> ppat pat) args)
    | PConstruct { name; args; record } ->
        C.AST.RecordPat (pglobal_ident_last name, pfield_pats args)
    | PConstant { lit } -> C.AST.Lit (pliteral lit)
    | PDeref { subpat } -> __TODO_pat__ p.span "deref"
    | _ -> .

  and pfield_pats (args : field_pat list) : (string * C.AST.pat) list =
    match args with
    | { field; pat } :: xs ->
        (pglobal_ident_last field, ppat pat) :: pfield_pats xs
    | _ -> []

  let operators =
    let c = GlobalIdent.of_string_exn in
    [
      (c "std::core::array::update_array_at", (3, [ ""; ".["; "]<-"; "" ]));
      (c "core::ops::index::Index::index", (2, [ ""; ".["; "]" ]));
      (c "core::ops::bit::BitXor::bitxor", (2, [ ""; ".^"; "" ]));
      (c "core::ops::bit::BitAnd::bitand", (2, [ ""; ".&"; "" ]));
      (c "core::ops::bit::BitOr::bitor", (2, [ ""; ".|"; "" ]));
      (c "core::ops::arith::Add::add", (2, [ ""; ".+"; "" ]));
      (c "core::ops::arith::Sub::sub", (2, [ ""; ".-"; "" ]));
      (c "core::ops::arith::Mul::mul", (2, [ ""; ".*"; "" ]));
      (`Primitive (BinOp Add), (2, [ ""; ".+"; "" ]));
      (`Primitive (BinOp Sub), (2, [ ""; ".-"; "" ]));
      (`Primitive (BinOp Mul), (2, [ ""; ".*"; "" ]));
      (`Primitive (BinOp Div), (2, [ ""; "./"; "" ]));
      (`Primitive (BinOp Eq), (2, [ ""; "=.?"; "" ]));
      (`Primitive (BinOp Lt), (2, [ ""; "<.?"; "" ]));
      (`Primitive (BinOp Le), (2, [ ""; "<=.?"; "" ]));
      (`Primitive (BinOp Ge), (2, [ ""; ">=.?"; "" ]));
      (`Primitive (BinOp Gt), (2, [ ""; ">.?"; "" ]));
      (`Primitive (BinOp Ne), (2, [ ""; "<>"; "" ]));
      (`Primitive (BinOp Rem), (2, [ ""; ".%"; "" ]));
      (`Primitive (BinOp BitXor), (2, [ ""; ".^"; "" ]));
      (`Primitive (BinOp BitAnd), (2, [ ""; ".&"; "" ]));
      (`Primitive (BinOp BitOr), (2, [ ""; ".|"; "" ]));
      (`Primitive (BinOp Shl), (2, [ ""; " shift_left "; "" ]));
      (`Primitive (BinOp Shr), (2, [ ""; " shift_right "; "" ]));
      (c "secret_integers::rotate_left", (2, [ "rol "; " "; "" ]));
      (c "hacspec::lib::foldi", (4, [ "foldi "; " "; " "; " "; "" ]));
      (* (c "secret_integers::u8", (0, ["U8"])); *)
      (* (c "secret_integers::u16", (0, ["U16"])); *)
      (* (c "secret_integers::u32", (0, ["U32"])); *)
      (* (c "secret_integers::u64", (0, ["U64"])); *)
      (* (c "secret_integers::u128", (0, ["U128"])); *)
    ]
    |> Map.of_alist_exn (module GlobalIdent)

  let index_of_field = function
    | `Concrete { path } -> (
        try Some (Int.of_string @@ Non_empty_list.last path) with _ -> None)
    | `TupleField (nth, _) -> Some nth
    | _ -> None

  (* let is_field_an_index = index_of_field >> Option.is_some *)

  let rec pexpr (e : expr) : C.AST.term =
    let span = e.span in
    match e.e with
    | Literal e -> C.AST.Const (pliteral e)
    | LocalVar local_ident -> C.AST.Name local_ident.name
    | GlobalVar (`TupleCons 0)
    | Construct { constructor = `TupleCons 0; fields = [] } ->
        C.AST.UnitTerm
    | GlobalVar global_ident -> C.AST.Var (pglobal_ident global_ident)
    | App
        {
          f = { e = GlobalVar (`Projector (`TupleField (n, len))) };
          args = [ arg ];
        } ->
        __TODO_term__ span "app global vcar projector tuple"
    | App { f = { e = GlobalVar x }; args } when Map.mem operators x ->
        let arity, op = Map.find_exn operators x in
        if List.length args <> arity then failwith "Bad arity";
        let args = List.map ~f:pexpr args in
        C.AST.AppFormat (op, args)
    (* | App { f = { e = GlobalVar x }; args } -> *)
    (*    __TODO_term__ span "GLOBAL APP?" *)
    | App { f; args } ->
        let base = pexpr f in
        let args = List.map ~f:pexpr args in
        C.AST.App (base, args)
    | If { cond; then_; else_ } ->
        C.AST.If
          ( pexpr cond,
            pexpr then_,
            Option.value_map else_ ~default:(C.AST.Literal "()") ~f:pexpr )
    | Array l -> C.AST.Array (List.map ~f:pexpr l)
    | Let { lhs; rhs; body; monadic = Some monad } ->
        C.AST.Let (ppat lhs, pexpr rhs, pexpr body, pty span lhs.typ)
    | Let { lhs; rhs; body; monadic = None } ->
        C.AST.Let (ppat lhs, pexpr rhs, pexpr body, pty span lhs.typ)
    | EffectAction _ -> __TODO_term__ span "monadic action"
    | Match { scrutinee; arms } ->
        C.AST.Match
          ( pexpr scrutinee,
            List.map
              ~f:(fun { arm = { pat; body } } -> (ppat pat, pexpr body))
              arms )
    | Ascription { e; typ } -> __TODO_term__ span "asciption"
    | Construct { constructor = `TupleCons 1; fields = [ (_, e) ]; base } ->
        pexpr e
    | Construct { constructor = `TupleCons n; fields; base } ->
        C.AST.Tuple (List.map ~f:(snd >> pexpr) fields)
    | Construct { constructs_record = true; constructor; fields; base } ->
        C.AST.RecordConstructor
          ( C.AST.Var (pglobal_ident constructor ^ "_t"),
            List.map ~f:(fun (f, e) -> (pglobal_ident f, pexpr e)) fields )
    | Construct { constructor; fields = [ (f, e) ]; base } ->
        C.AST.App (C.AST.Var (pglobal_ident constructor), [ pexpr e ])
    | Construct { constructor; fields; base } ->
        C.AST.Var
          (pglobal_ident constructor ^ snd (ty_to_string (pty span e.typ)))
    | Closure { params; body } ->
        C.AST.Lambda (List.map ~f:ppat params, pexpr body)
    | MacroInvokation { macro; args; witness } ->
        Error.raise
        @@ {
             kind = UnsupportedMacro { id = [%show: global_ident] macro };
             span = e.span;
           }
    | _ -> .

  let rec pitem (e : item) : C.AST.decl list =
    let span = e.span in
    match e.v with
    | Fn { name; generics; body; params } ->
        [
          C.AST.Definition
            ( pglobal_ident name,
              List.map
                ~f:(fun { pat; typ; typ_span } -> (ppat pat, pty span typ))
                params,
              pexpr body,
              pty span body.typ );
        ]
    | TyAlias { name; generics; ty } ->
        [ C.AST.Notation (pglobal_ident name ^ "_t", pty span ty) ]
    (* record *)
    | Type
        {
          name;
          generics;
          variants = [ { name = record_name; arguments } ];
          record = true;
        }
      when GlobalIdent.equal name record_name ->
        [
          C.AST.Record
            ( pglobal_ident_last name ^ "_t" ^ pglobal_ident record_name,
              p_record_record span arguments );
        ]
    (* enum *)
    | Type { name; generics; variants; record = true } ->
        [
          C.AST.Inductive
            ( pglobal_ident_last name ^ "_t",
              List.fold_left ~init:[]
                ~f:(fun a b ->
                  a
                  @ [
                      (match b with
                      | GPType { ident; default } -> ident.name
                      | _ -> failwith "Coq: TODO: generic_params");
                    ])
                generics.params,
              p_inductive span variants name );
        ]
    | Type { name; generics; variants } ->
        [
          C.AST.Notation
            ( pglobal_ident_last name ^ "_t",
              C.AST.Product (List.map ~f:snd (p_record span variants name)) );
          C.AST.Definition
            ( pglobal_ident_last name,
              [],
              C.AST.Var "id",
              C.AST.Arrow
                ( C.AST.Name (pglobal_ident_last name ^ "_t"),
                  C.AST.Name (pglobal_ident_last name ^ "_t") ) );
        ]
    | IMacroInvokation
        {
          macro =
            `Concrete
              Non_empty_list.
                { crate = "hacspec_lib_tc"; path = [ "public_nat_mod" ] };
          argument;
          span;
        } ->
        let open Hacspeclib_macro_parser in
        let o : PublicNatMod.t =
          PublicNatMod.parse argument |> Result.ok_or_failwith
        in
        [
          C.AST.Notation
            ( o.type_name ^ "_t",
              C.AST.NatMod
                (o.type_of_canvas, o.bit_size_of_field, o.modulo_value) );
          C.AST.Definition
            ( o.type_name,
              [],
              C.AST.Var "id",
              C.AST.Arrow
                ( C.AST.Name (o.type_name ^ "_t"),
                  C.AST.Name (o.type_name ^ "_t") ) );
        ]
    | IMacroInvokation
        {
          macro =
            `Concrete
              Non_empty_list.{ crate = "hacspec_lib_tc"; path = [ "bytes" ] };
          argument;
          span;
        } ->
        let open Hacspeclib_macro_parser in
        let o : Bytes.t = Bytes.parse argument |> Result.ok_or_failwith in
        [
          C.AST.Notation
            ( o.bytes_name ^ "_t",
              C.AST.ArrayTy (C.AST.Int (C.AST.U8, false), o.size) );
          C.AST.Definition
            ( o.bytes_name,
              [],
              C.AST.Var "id",
              C.AST.Arrow
                ( C.AST.Name (o.bytes_name ^ "_t"),
                  C.AST.Name (o.bytes_name ^ "_t") ) );
        ]
    | IMacroInvokation
        {
          macro =
            `Concrete
              Non_empty_list.
                {
                  crate = "hacspec_lib_tc";
                  path = [ "unsigned_public_integer" ];
                };
          argument;
          span;
        } ->
        let open Hacspeclib_macro_parser in
        let o = UnsignedPublicInteger.parse argument |> Result.ok_or_failwith in
        [
          C.AST.Notation
            ( o.integer_name ^ "_t",
              C.AST.ArrayTy
                (C.AST.Int (C.AST.U8, false), Int.to_string ((o.bits + 7) / 8))
            );
          C.AST.Definition
            ( o.integer_name,
              [],
              C.AST.Var "id",
              C.AST.Arrow
                ( C.AST.Name (o.integer_name ^ "_t"),
                  C.AST.Name (o.integer_name ^ "_t") ) );
        ]
    | IMacroInvokation
        {
          macro =
            `Concrete
              Non_empty_list.
                { crate = "hacspec_lib_tc"; path = [ "public_bytes" ] };
          argument;
          span;
        } ->
        let open Hacspeclib_macro_parser in
        let o : Bytes.t = Bytes.parse argument |> Result.ok_or_failwith in
        let typ = C.AST.ArrayTy (C.AST.Int (C.AST.U8, false), o.size) in
        [
          C.AST.Notation (o.bytes_name ^ "_t", typ);
          C.AST.Definition
            ( o.bytes_name,
              [],
              C.AST.Var "id",
              C.AST.Arrow
                ( C.AST.Name (o.bytes_name ^ "_t"),
                  C.AST.Name (o.bytes_name ^ "_t") ) );
        ]
    | IMacroInvokation
        {
          macro =
            `Concrete
              Non_empty_list.{ crate = "hacspec_lib_tc"; path = [ "array" ] };
          argument;
          span;
        } ->
        let open Hacspeclib_macro_parser in
        let o : Array.t = Array.parse argument |> Result.ok_or_failwith in
        let typ =
          match o.typ with
          (* Some *)
          | "U128" -> C.AST.U128
          (* Some *)
          | "U64" -> C.AST.U64
          (* Some *)
          | "U32" -> C.AST.U32
          (* Some *)
          | "U16" -> C.AST.U16
          (* Some *)
          | "U8" -> C.AST.U8
          | usize -> C.AST.U32 (* TODO: usize? *)
        in
        [
          C.AST.Notation
            ( o.array_name ^ "_t",
              C.AST.ArrayTy (C.AST.Int (typ, false), (* int_of_string *) o.size)
            );
          C.AST.Definition
            ( o.array_name,
              [],
              C.AST.Var "id",
              C.AST.Arrow
                ( C.AST.Name (o.array_name ^ "_t"),
                  C.AST.Name (o.array_name ^ "_t") ) );
        ]
    | IMacroInvokation { macro; _ } ->
        Error.raise
        @@ {
             kind = UnsupportedMacro { id = [%show: global_ident] macro };
             span = e.span;
           }
    | Use { path; is_external; rename } ->
        if is_external then [] else [ C.AST.Require (path, rename) ]
    | HaxError s -> [ __TODO_item__ span s ]
    | NotImplementedYet -> [ __TODO_item__ span "Not implemented yet?" ]
    | Trait { name; generics; items } ->
        [
          C.AST.Class
            ( pglobal_ident name,
              List.map
                ~f:(fun x ->
                  ( x.ti_name,
                    match x.ti_v with
                    | TIFn fn_ty -> pty span fn_ty
                    | _ -> __TODO_ty__ span "field_ty" ))
                items,
              List.fold_left ~init:[]
                ~f:(fun a b ->
                  a
                  @ [
                      (match b with
                      | GPType { ident; default } -> ident.name
                      | _ -> failwith "Coq: TODO: generic_params");
                    ])
                generics.params );
        ]
    | Impl { generics; self_ty; of_trait = Some (name, gen_vals); items } ->
        [
          C.AST.Instance
            ( pglobal_ident name,
              pty span self_ty,
              args_ty span gen_vals,
              List.map
                ~f:(fun x ->
                  match x.ii_v with
                  | IIFn { body; params } ->
                      ( x.ii_name,
                        List.map
                          ~f:(fun { pat; typ; typ_span } ->
                            (ppat pat, pty span typ))
                          params,
                        pexpr body,
                        pty span body.typ )
                  | _ ->
                      ( "todo_name",
                        [],
                        __TODO_term__ span "body",
                        __TODO_ty__ span "typ" ))
                items );
        ]
    | Impl _ -> [ __TODO_item__ span "trait self" ]

  (* self_ty : ty; *)
  (* of_trait : (global_ident * generic_value list) option; *)
  (* items : impl_item list; *)

  and p_inductive span variants parrent_name : C.AST.inductive_case list =
    match variants with
    | { name; arguments = [ (arg_name, arg_ty) ] } :: xs ->
        if (index_of_field >> Option.is_some) arg_name then
          C.AST.InductiveCase (pglobal_ident_last name, pty span arg_ty)
          :: p_inductive span xs parrent_name
        else
          C.AST.InductiveCase (pglobal_ident_last arg_name, pty span arg_ty)
          :: p_inductive span xs parrent_name
    | { name; arguments = [] } :: xs ->
        C.AST.BaseCase (pglobal_ident_last name)
        :: p_inductive span xs parrent_name
    | { name; arguments } :: xs ->
        C.AST.InductiveCase
          ( pglobal_ident_last name,
            C.AST.RecordTy (pglobal_ident name, p_record_record span arguments)
          )
        :: p_inductive span xs parrent_name
    | _ -> []

  and p_record span variants parrent_name : (string * C.AST.ty) list =
    match variants with
    | { name; arguments = [ (arg_name, arg_ty) ] } :: xs ->
        (pglobal_ident_last arg_name, pty span arg_ty)
        :: p_record span xs parrent_name
    | { name; arguments = [] } :: xs ->
        ("TODO FIELD?", __TODO_ty__ span "TODO")
        :: p_record span xs parrent_name
    | { name; arguments } :: xs ->
        ( pglobal_ident_last name,
          C.AST.RecordTy (pglobal_ident name, p_record_record span arguments) )
        :: p_record span xs parrent_name
    | _ -> []

  and p_record_record span arguments : (string * C.AST.ty) list =
    List.map
      ~f:(function
        | arg_name, arg_ty -> (pglobal_ident_last arg_name, pty span arg_ty))
      arguments
end

module type S = sig
  val pitem : item -> C.AST.decl list
end

let make ctx =
  (module Make (struct
    let ctx = ctx
  end) : S)

let string_of_item (item : item) : string =
  let (module Print) = make { current_namespace = item.parent_namespace } in
  List.map ~f:decl_to_string @@ Print.pitem item |> String.concat ~sep:"\n"

let string_of_items =
  List.map ~f:string_of_item >> List.map ~f:String.strip
  >> List.filter ~f:(String.is_empty >> not)
  >> String.concat ~sep:"\n\n"

let hardcoded_coq_headers =
  "(* File automatically generated by Hacspec *)\n\
   From Hacspec Require Import Hacspec_Lib MachineIntegers.\n\
   From Coq Require Import ZArith.\n\
   Import List.ListNotations.\n\
   Open Scope Z_scope.\n\
   Open Scope bool_scope.\n"

let translate (bo : BackendOptions.t) (items : AST.item list) :
    Raw_thir_ast.file list =
  U.group_items_by_namespace items
  |> Map.to_alist
  |> List.map ~f:(fun (ns, items) ->
         let mod_name =
           String.concat ~sep:"."
             (List.map
                ~f:(map_first_letter String.uppercase)
                (fst ns :: snd ns))
         in

         Raw_thir_ast.
           {
             path = mod_name ^ ".v";
             contents =
               hardcoded_coq_headers ^ "\n" ^ string_of_items items ^ "\n";
           })

open Phase_utils

module TransformToInputLanguage =
  CatchErrors
    ([%functor_application
    Phases.Reject.RawOrMutPointer(Features.Rust)
    |> Phases.Reject.Arbitrary_lhs
    |> Phases.Reconstruct_for_loops
    |> Phases.Direct_and_mut
    |> Phases.Reject.Continue
    |> Phases.Drop_references
    |> Phases.Trivialize_assign_lhs
    |> Phases.Reconstruct_question_marks
    |> Side_effect_utils.Hoist
    |> Phases.Local_mutation
    |> Phases.Reject.Continue
    |> Phases.Cf_into_monads
    |> Phases.Reject.EarlyExit
    |> Phases.Functionalize_loops
    |> RejectNotCoq
    |> Identity
    ]
    [@ocamlformat "disable"])

let apply_phases (bo : BackendOptions.t) (i : Ast.Rust.item) : AST.item list =
  TransformToInputLanguage.ditem i

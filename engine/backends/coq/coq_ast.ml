open Hax_engine
open Utils
open Base

module type Library = sig
  module Notation : sig
    val int_repr : string -> string -> string
    val let_stmt : string -> string -> string -> string -> int -> string
    val let_mut_stmt : string -> string -> string -> string -> int -> string
    val tuple_prefix : string
  end
end

module Coq =
functor
  (Lib : Library)
  ->
  struct
    module AST = struct
      type int_size = U8 | U16 | U32 | U64 | U128 | USize
      type int_type = { size : int_size; signed : bool }

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
        | Let of { pattern : pat; mut : bool; value : term; body : term; value_typ : ty }
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
        | ProgramDefinition of definition_type
        | Notation of string * ty
        | Record of string * (string * ty) list
        | Inductive of string * generics_type * inductive_case list
        | Class of string * (string * ty) list * generics_type
        | Instance of string * ty * ty list * definition_type list
        | Require of string list * string option
    end

    let __TODO_pat__ s = AST.Ident (s ^ " todo(pat)")
    let __TODO_ty__ s : AST.ty = AST.Name (s ^ " todo(ty)")
    let __TODO_term__ s = AST.Const (AST.Const_string (s ^ " todo(term)"))
    let __TODO_item__ s = AST.Unimplemented (s ^ " todo(item)")

    let int_size_to_string (x : AST.int_size) : string =
      match x with
      | AST.U8 -> "8"
      | AST.U16 -> "16"
      | AST.U32 -> "32"
      | AST.U64 -> "64"
      | AST.U128 -> "128"
      | AST.USize -> "32"

    let rec ty_to_string (x : AST.ty) : AST.decl list * string =
      match x with
      | AST.Wild -> ([], "_")
      | AST.Bool -> ([], "bool")
      | AST.Unit -> ([], "unit")
      | AST.Int { size = AST.USize; signed } -> ([], "uint_size")
      | AST.Int { size; signed } -> ([], "int" ^ int_size_to_string size)
      | AST.Name s -> ([], s)
      | AST.RecordTy (name, fields) -> ([ AST.Record (name, fields) ], name)
      | AST.Product [] -> ([], "unit")
      | AST.Product l ->
          let p_decl, p_str = product_to_string l (" " ^ "×" ^ " ") in
          (p_decl, "(" ^ p_str ^ ")")
      | AST.Arrow (a, b) ->
          let a_ty_def, a_ty_str = ty_to_string a in
          let b_ty_def, b_ty_str = ty_to_string b in
          (a_ty_def @ b_ty_def, a_ty_str ^ " " ^ "->" ^ " " ^ b_ty_str)
      | AST.ArrayTy (t, l) ->
          let ty_def, ty_str = ty_to_string t in
          (ty_def, "nseq" ^ " " ^ ty_str ^ " " ^ (* Int.to_string *) l)
      | AST.SliceTy t ->
          let ty_def, ty_str = ty_to_string t in
          (ty_def, "seq" ^ " " ^ ty_str)
      | AST.AppTy (i, []) -> ([], i)
      (* | AST.AppTy (i, [ y ]) -> *)
      (*     let ty_defs, ty_str = ty_to_string y in *)
      (*     (ty_defs, i ^ " " ^ ty_str) *)
      | AST.AppTy (i, p) ->
          let ty_def, ty_str = product_to_string p ") (" in
          (ty_def, i ^ " " ^ "(" ^ ty_str ^ ")")
      | AST.NatMod (t, i, s) ->
          ( [
              AST.Notation
                ( t,
                  AST.ArrayTy
                    (AST.Int { size = U8; signed = false }, Int.to_string i) );
            ],
            "nat_mod 0x" ^ s )
      | _ -> .

    and product_to_string (x : AST.ty list) (sep : string) :
        AST.decl list * string =
      match x with
      | [ y ] -> ty_to_string y
      | y :: ys ->
          let ty_defs, ty_str = ty_to_string y in
          let ys_defs, ys_str = product_to_string ys sep in
          (ty_defs @ ys_defs, ty_str ^ sep ^ ys_str)
      | [] -> ([], "")
    (* and record_fields_to_string (x : (string * AST.ty) list) : AST.decl list * string = *)
    (*   match x with *)
    (*   | (name, ty) :: xs -> *)
    (*      let ty_def, ty_str = ty_to_string ty in *)
    (*      let xs_def, xs_str = record_fields_to_string xs in *)
    (*      ty_def @ xs_def, newline_indent 1 ^ name ^ ":" ^ " " ^ ty_str ^ ";" ^ xs_str *)
    (*   | _ -> [], "" *)

    let literal_to_string (x : AST.literal) : string =
      match x with
      | Const_string s -> s
      | Const_char c -> Int.to_string c (* TODO *)
      | Const_int (i, { size; signed }) ->
          Lib.Notation.int_repr (int_size_to_string size) i
      (*  *)
      | Const_bool b -> Bool.to_string b

    let rec pat_to_string (x : AST.pat) (is_top_expr : bool) depth : string =
      match x with
      | AST.Wild -> "_"
      | AST.UnitPat -> tick_if is_top_expr ^ "tt"
      | AST.Ident s -> s
      | AST.Lit l -> literal_to_string l
      | AST.RecordPat (name, args) ->
          (* name ^ " " ^ *)
          "{|"
          ^ record_pat_to_string args (depth + 1)
          ^ newline_indent depth ^ "|}"
      | AST.TuplePat vals ->
          tick_if is_top_expr ^ "(" ^ tuple_pat_to_string vals (depth + 1) ^ ")"
      | AST.AscriptionPat (p, ty) ->
          pat_to_string p true depth (* TODO: Should this be true of false? *)

    and tick_if is_top_expr = if is_top_expr then "'" else ""

    and tuple_pat_to_string vals depth =
      match vals with
      | [ t ] -> pat_to_string t false depth
      | t :: ts ->
          pat_to_string t false depth ^ "," ^ tuple_pat_to_string ts depth
      | [] -> "todo empty tuple pattern?"

    and record_pat_to_string args depth : string =
      match args with
      | (name, pat) :: xs ->
          newline_indent depth ^ name ^ " " ^ ":=" ^ " "
          ^ pat_to_string pat true depth
          ^ ";"
          ^ record_pat_to_string xs depth
      | _ -> ""

    let rec term_to_string (x : AST.term) depth : string * bool =
      match x with
      | AST.UnitTerm -> ("tt", false)
      | AST.Let { pattern = pat; mut; value = bind; value_typ = typ; body = term } ->
          let _, ty_str = ty_to_string typ in
          (* TODO: propegate type definition *)
          ( (if mut then Lib.Notation.let_mut_stmt else Lib.Notation.let_stmt)
              (pat_to_string pat true depth)
              (term_to_string_without_paren bind (depth + 1))
              ty_str
              (term_to_string_without_paren term depth)
              depth,
            true )
      | AST.If (cond, then_, else_) ->
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
      | AST.Match (match_val, arms) ->
          ( "match" ^ " "
            ^ term_to_string_without_paren match_val (depth + 1)
            ^ " " ^ "with" ^ newline_indent depth ^ arm_to_string arms depth
            ^ "end",
            false )
      | AST.Const c -> (literal_to_string c, false)
      | AST.Literal s -> (s, false)
      | AST.AppFormat (format, args) ->
          ( format_to_string format
              (List.map ~f:(fun x -> term_to_string_with_paren x depth) args),
            true (* TODO? Notation does not always need paren *) )
      | AST.App (f, args) ->
          let f_s, f_b = term_to_string f depth in
          (f_s ^ args_to_string args depth, f_b || List.length args > 0)
      | AST.Var s -> (s, false)
      | AST.Name s -> (s, false)
      | AST.RecordConstructor (f, args) ->
          ( "Build_"
            ^ term_to_string_without_paren f depth
            ^ " "
            ^ record_args_to_string args depth,
            true )
      | AST.Type t ->
          let _, ty_str = ty_to_string t in
          (* TODO: Make definitions? *)
          (ty_str, true (* TODO? does this always need paren? *))
      | AST.Lambda (params, body) ->
          ( lambda_params_to_string params depth
            ^ newline_indent (depth + 1)
            ^ term_to_string_without_paren body (depth + 1),
            true )
      | AST.Tuple vals ->
          ( Lib.Notation.tuple_prefix ^ "("
            ^ tuple_term_to_string vals (depth + 1)
            ^ ")",
            false )
          (* List.fold_left ~init:(term_to_string_without_paren t (depth+1)) ~f:(fun x y -> "(" ^ x ^ "," ^ term_to_string_without_paren y (depth+1) ^ ")") ts, false *)
      | AST.Array (t :: ts) ->
          ( "array_from_list" ^ " " ^ "["
            ^ List.fold_left
                ~init:(term_to_string_without_paren t (depth + 1))
                ~f:(fun x y ->
                  x ^ ";"
                  ^ newline_indent (depth + 1)
                  ^ term_to_string_without_paren y (depth + 1))
                ts
            ^ "]",
            true )
      | AST.Array [] -> ("!TODO empty array!", false)
      | _ -> .

    and tuple_term_to_string vals depth : string =
      match vals with
      | [ t ] -> term_to_string_without_paren t depth
      | t :: ts ->
          term_to_string_without_paren t depth
          ^ ","
          ^ tuple_term_to_string ts depth
      | [] -> "!TODO empty tuple!"

    and lambda_params_to_string (params : AST.pat list) depth : string =
      match params with
      | x :: xs ->
          "fun" ^ " " ^ pat_to_string x true depth ^ " " ^ "=>"
          ^ lambda_params_to_string xs depth
      | [] -> ""

    and term_to_string_with_paren (x : AST.term) depth : string =
      let s, b = term_to_string x depth in
      if b then "(" ^ s ^ ")" else s

    and term_to_string_without_paren (x : AST.term) depth : string =
      let s, _ = term_to_string x depth in
      s

    and format_to_string (format : string list) (args : string list) : string =
      match format with
      | f :: fs -> (
          match args with x :: xs -> f ^ x ^ format_to_string fs xs | [] -> f)
      | [] -> failwith "incorrect formatting"

    and record_args_to_string (args : (string * AST.term) list) depth : string =
      match args with
      | (i, t) :: xs ->
          term_to_string_with_paren t depth ^ record_args_to_string xs depth
      | _ -> ""

    and args_to_string (args : AST.term list) depth : string =
      match args with
      | x :: xs ->
          " " ^ term_to_string_with_paren x depth ^ args_to_string xs depth
      | _ -> ""

    and arm_to_string (x : (AST.pat * AST.term) list) depth : string =
      match x with
      | (pat, body) :: xs ->
          "|" ^ " "
          ^ pat_to_string pat true depth
          ^ " " ^ "=>" ^ " "
          ^ term_to_string_without_paren body (depth + 1)
          ^ newline_indent depth ^ arm_to_string xs depth
      | _ -> ""

    let rec decl_to_string (x : AST.decl) : string =
      match x with
      | AST.Unimplemented s -> "(*" ^ s ^ "*)"
      | AST.Definition (name, params, term, ty) ->
          let definitions, ty_str = ty_to_string ty in
          decl_list_to_string definitions
          ^ "Definition" ^ " " ^ name ^ " " ^ params_to_string params ^ ":"
          ^ " " ^ ty_str ^ " " ^ ":=" ^ newline_indent 1
          ^ term_to_string_without_paren term 1
          ^ "."
      | AST.ProgramDefinition (name, params, term, ty) ->
          let definitions, ty_str = ty_to_string ty in
          decl_list_to_string definitions
          ^ "Program" ^ " " ^ "Definition" ^ " " ^ name ^ " "
          ^ params_to_string params ^ ":" ^ " " ^ ty_str ^ " " ^ ":="
          ^ newline_indent 1
          ^ term_to_string_without_paren term 1
          ^ " " ^ ":" ^ " " ^ ty_str ^ "." ^ newline_indent 0 ^ "Fail" ^ " "
          ^ "Next" ^ " " ^ "Obligation."
      | AST.Notation (name, ty) ->
          let definitions, ty_str = ty_to_string ty in
          decl_list_to_string definitions
          ^ "Notation" ^ " " ^ name ^ " " ^ ":=" ^ " " ^ "(" ^ ty_str ^ ")"
          ^ "."
      | AST.Record (name, variants) ->
          let definitions, variants_str =
            variants_to_string variants (newline_indent 1) ";"
          in
          decl_list_to_string definitions
          ^ "Record" ^ " " ^ name ^ " " ^ ":" ^ " " ^ "Type" ^ " " ^ ":=" ^ "{"
          ^ variants_str ^ newline_indent 0 ^ "}."
      | AST.Inductive (name, generics, variants) ->
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
      | AST.Class (name, trait_items, generics) ->
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
      | AST.Instance (name, self_ty, ty_list, impl_list) ->
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
                x ^ newline_indent 1 ^ name ^ " " ^ params_to_string params
                ^ ":=" ^ " "
                ^ term_to_string_without_paren term 1
                ^ ";")
              impl_list
          in
          let ty_defs, ty_str = ty_to_string self_ty in
          decl_list_to_string (ty_list_defs @ ty_defs)
          ^ "Instance" ^ " " ^ ty_str ^ "_" ^ name ^ " " ^ ":" ^ " " ^ name
          ^ " " ^ ty_list_str ^ ":=" ^ " " ^ "{" ^ impl_str ^ newline_indent 0
          ^ "}" ^ "."
      | AST.Require ([], rename) -> ""
      | AST.Require (import :: imports, rename) -> (
          "Require Import" ^ " "
          ^ map_first_letter String.uppercase import
            (* (List.fold_left ~init:import ~f:(fun x y -> x ^ "." ^ y) imports) *)
          ^ "."
          ^ match rename with Some s -> " (* " ^ "as " ^ s ^ " *)" | _ -> "")

    and decl_list_to_string (x : AST.decl list) : string =
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

    and inductive_case_to_string variants pre post : AST.decl list * string =
      match variants with
      | x :: xs ->
          let ty_def, mid_str =
            match x with
            | AST.BaseCase ty_name -> ([], ty_name)
            | AST.InductiveCase (ty_name, ty) ->
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
        AST.decl list * string =
      List.fold_left ~init:([], "")
        ~f:(fun y x ->
          let mid_str, ty_str =
            match x with
            | AST.BaseCase ty_name -> (ty_name, "")
            | AST.InductiveCase (ty_name, ty) ->
                let _, ty_str = ty_to_string ty in
                (ty_name, " " ^ ty_str)
          in
          match y with
          | variant_definitions, variants_str ->
              ( variant_definitions,
                pre ^ mid_str ^ mid ^ ty_str ^ post ^ variants_str ))
        variants

    and variants_to_string variants pre post : AST.decl list * string =
      List.fold_left ~init:([], "")
        ~f:(fun (variant_definitions, variants_str) (ty_name, ty) ->
          let ty_definitions, ty_str = ty_to_string ty in
          ( ty_definitions @ variant_definitions,
            pre ^ ty_name ^ " " ^ ":" ^ " " ^ ty_str ^ post ^ variants_str ))
        variants
  end

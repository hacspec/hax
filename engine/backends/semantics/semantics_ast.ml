open Hax_engine
open Utils
open Base

(* Dependent type theory with *)
(*
   - all finite limits : (A^b) and (_ * _) and 1
   - telescope types: records
   - and co-products: (_ + _) and 0 (enums)
   - booleans : 2 object
*)
module Semantics = struct
  module AST = struct
    type ty =
      | Unimplemented of string
      (* Values *)
      | Wild
      | Unit
      | Bool
      | Int
      | List of ty
      | Product of ty list
      (* Varibles *)
      | Name of string
      (* Higher order *)
      | AppTy of ty * ty
      | Arrow of ty * ty

    type pat =
      | Unimplemented of string
      (* Value patterns *)
      | WildPat
      | UnitPat
      | BoolPat of bool
      | IntPat of int
      | RecordPat of string * (string * pat) list
      | EnumPat of string * pat list
      | ProductPat of pat list
      (* pat with variable *)
      | Ident of string
      | TypedPat of pat * ty

    type term =
      | Unimplemented of string
      (* Values *)
      | UnitTerm
      | BoolTerm of bool
      | IntTerm of int
      | RecordTerm of term * (string * term) list
      | ProductTerm of term list
      | Array of term list
      (* Variables *)
      | Ident of string
      | Let of { pattern : pat; value : term; body : term; value_typ : ty }
      | App of term * term
      | Set of term * (string * term)
      (* Higher order *)
      | Lambda of pat list * term
      | Type of ty
      (* Control flow *)
      | If of term * term * term
      | Match of term * (pat * term) list

    type decl =
      | Unimplemented of string
      | Annotation of string
      | Definition of string * term
      | Section of string * decl list
  end

  let rec type_to_string (x : AST.ty) : string * bool =
    match x with
    | Unimplemented x -> ("Unimplemented" ^ " " ^ x, true)
    (* Values *)
    | Wild -> ("_", false)
    | Unit -> ("unit", false)
    | Bool -> ("bool", false)
    | Int -> ("int", false)
    | List t -> (type_to_string_with_paren t ^ " " ^ "list", false)
    | Product l ->
        ( String.concat ~sep:"*" (List.map ~f:type_to_string_without_paren l),
          true )
    (* Varibles *)
    | Name s -> (s, false)
    (* Higher order *)
    | AppTy (a, b) ->
        (type_to_string_with_paren a ^ " " ^ type_to_string_with_paren b, true)
    | Arrow (a, b) ->
        ( type_to_string_with_paren a
          ^ " " ^ "->" ^ " "
          ^ type_to_string_with_paren b,
          true )

  and type_to_string_with_paren (x : AST.ty) : string =
    let s, b = type_to_string x in
    if b then "(" ^ s ^ ")" else s

  and type_to_string_without_paren (x : AST.ty) : string =
    let s, _ = type_to_string x in
    s

  let rec pat_to_string (x : AST.pat) : string * bool =
    match x with
    | Unimplemented x -> ("Unimplemented" ^ " " ^ x, true)
    (* Value patterns *)
    | WildPat -> ("_", false)
    | UnitPat -> ("tt", false)
    | BoolPat true -> ("true", false)
    | BoolPat false -> ("false", false)
    | IntPat i -> (Int.to_string i, false)
    | RecordPat (name, values) -> ("TODO RecordPat", true)
    | EnumPat (name, args) -> ("TODO EnumPat", true)
    | ProductPat pats ->
        ( "("
          ^ String.concat ~sep:","
              (List.map ~f:pat_to_string_without_paren pats)
          ^ ")",
          false )
    (* pat with variable *)
    | Ident s -> (s, false)
    | TypedPat (p, t) ->
        ( pat_to_string_without_paren p
          ^ " " ^ ":" ^ " "
          ^ type_to_string_without_paren t,
          true )

  and pat_to_string_with_paren (x : AST.pat) : string =
    let s, b = pat_to_string x in
    if b then "(" ^ s ^ ")" else s

  and pat_to_string_without_paren (x : AST.pat) : string =
    let s, _ = pat_to_string x in
    s

  let rec term_to_string (x : AST.term) : string * bool =
    match x with
    | Unimplemented x -> ("Unimplemented" ^ " " ^ x, true)
    (* Values *)
    | UnitTerm -> ("tt", false)
    | BoolTerm true -> ("true", false)
    | BoolTerm false -> ("false", false)
    | IntTerm i -> (Int.to_string i, false)
    | RecordTerm (x, l) -> ("TODO RECORD", true)
    | ProductTerm l ->
        ( "("
          ^ String.concat ~sep:"," (List.map ~f:term_to_string_without_paren l)
          ^ ")",
          false )
    | Array l ->
        ( "["
          ^ String.concat ~sep:"," (List.map ~f:term_to_string_without_paren l)
          ^ "]",
          false )
    (* Variables *)
    | Ident x -> (x, false)
    | Let { pattern; value; body; value_typ } ->
        ( "let" ^ " "
          ^ pat_to_string_without_paren pattern
          ^ " " ^ ":=" ^ " "
          ^ term_to_string_without_paren value
          ^ " " ^ "in" ^ "\n"
          ^ term_to_string_without_paren body,
          false )
    | App (x, y) ->
        (term_to_string_with_paren x ^ " " ^ term_to_string_with_paren y, true)
    | Set (x, (n, y)) ->
        ( term_to_string_with_paren x
          ^ "[" ^ n ^ " " ^ ":=" ^ " "
          ^ term_to_string_without_paren y
          ^ "]",
          false )
    (* Higher order *)
    | Lambda (args, body) ->
        ( "λ" ^ " "
          ^ String.concat ~sep:" " (List.map ~f:pat_to_string_with_paren args)
          ^ "," ^ " "
          ^ term_to_string_without_paren body,
          true )
    | Type ty -> ("TODO TY", true)
    (* Control flow *)
    | If (cond, e_then, e_else) -> ("TODO IF", true)
    | Match (v, arms) -> ("TODO MATCH", true)

  and term_to_string_with_paren (x : AST.term) : string =
    let s, b = term_to_string x in
    if b then "(" ^ s ^ ")" else s

  and term_to_string_without_paren (x : AST.term) : string =
    let s, _ = term_to_string x in
    s

  let rec decl_to_string (x : AST.decl) : string =
    match x with
    | Unimplemented x -> "(" ^ "Unimplemented" ^ " " ^ x ^ ")"
    | Annotation x -> x
    | Definition (name, value) ->
        "Definition" ^ " " ^ name ^ " " ^ ":= "
        ^ term_to_string_without_paren value
    | Section (name, decls) ->
        "Section" ^ " " ^ name ^ "\n"
        ^ String.concat ~sep:"\n" (List.map ~f:decl_to_string decls)
        ^ "\n" ^ "End" ^ " " ^ name
end

open Hax_engine
open Utils
open Base

(* (Pure) Dependent type theory with *)
(*
   - all finite limits : (A^b) and (_ * _) and 1
   - telescope types: records
   - and co-products: (_ + _) and 0 (enums)
   - booleans : 2 object
   - natural number objects : 1 -0-> N -S-> N
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
      | Array of ty * term
      | Product of ty list
      | Record of (string * ty) list
      (* Varibles *)
      | Name of string
      (* Higher order *)
      | AppTy of ty * ty
      | Arrow of ty * ty

    and pat =
      | Unimplemented of string
      (* Value patterns *)
      | WildPat
      | UnitPat
      | BoolPat of bool
      | IntPat of int
      | RecordPat of string * (string * pat) list
      | ListPat of pat list
      | EnumPat of string * pat list
      | ProductPat of pat list
      (* pat with variable *)
      | Ident of string
      | TypedPat of pat * ty

    and term =
      | Unimplemented of string
      (* Values *)
      | UnitTerm
      | BoolTerm of bool
      | IntTerm of int
      | RecordTerm of term * (string * term) list
      | ProductTerm of term list * int
      | Array of term list
      (* Variables *)
      | Ident of string
      | Let of { pattern : pat; value : term; body : term; value_typ : ty }
      | App of term * term
      | Set of term * (string * term)
      (* Higher order *)
      | Lambda of (pat list * term) list
      | Type of ty
      | TypedTerm of term * ty

    type decl =
      | Unimplemented of string
      | Annotation of string
      | Macro of string * string list
      | Definition of string * term
      | TypeDefinition of string * ty
      | Section of string * decl list
      | Import of string
  end

  let rec type_to_string (x : AST.ty) ~depth : string * bool =
    match x with
    | Unimplemented x -> ("Unimplemented" ^ " " ^ x, true)
    (* Values *)
    | Wild -> ("_", false)
    | Unit -> ("unit", false)
    | Bool -> ("bool", false)
    | Int -> ("int", false)
    | List t -> (type_to_string_with_paren t ~depth ^ " " ^ "list", false)
    | Array (t, e) -> (type_to_string_with_paren t ~depth ^ " " ^ "array<" ^ term_to_string_without_paren e ~depth ^ ">", false)
    | Product l ->
        ( String.concat ~sep:"*" (List.map ~f:(type_to_string_without_paren ~depth) l),
          true )
    | Record l ->
      ("{" ^
       String.concat ~sep:(";" ^ " ") (List.map ~f:(fun (n,t) -> n ^ " " ^ ":" ^ " " ^ type_to_string_without_paren t ~depth) l)
       ^ "}", false)
    (* Varibles *)
    | Name s -> (s, false)
    (* Higher order *)
    | AppTy (a, b) ->
        (type_to_string_with_paren a ~depth ^ " " ^ type_to_string_with_paren b ~depth, true)
    | Arrow (a, b) ->
        ( type_to_string_with_paren a ~depth
          ^ " " ^ "->" ^ " "
          ^ type_to_string_with_paren b ~depth,
          true )

  and type_to_string_with_paren (x : AST.ty) ~depth : string =
    let s, b = type_to_string x ~depth in
    if b then "(" ^ s ^ ")" else s

  and type_to_string_without_paren (x : AST.ty) ~depth : string =
    let s, _ = type_to_string x ~depth in
    s

  and pat_to_string (x : AST.pat) ~depth : string * bool =
    match x with
    | Unimplemented x -> ("Unimplemented" ^ " " ^ x, true)
    (* Value patterns *)
    | WildPat -> ("_", false)
    | UnitPat -> ("tt", false)
    | BoolPat true -> ("true", false)
    | BoolPat false -> ("false", false)
    | IntPat i -> (Int.to_string i, false)
    | RecordPat (name, values) -> ("TODO RecordPat", true)
    | ListPat pats -> ("[" ^ String.concat ~sep:"," (List.map ~f:(pat_to_string_without_paren ~depth) pats) ^ "]", false)
    | EnumPat (name, args) -> ("TODO EnumPat", true)
    | ProductPat pats ->
        ( "("
          ^ String.concat ~sep:","
              (List.map ~f:(pat_to_string_without_paren ~depth) pats)
          ^ ")",
          false )
    (* pat with variable *)
    | Ident s -> (s, false)
    | TypedPat (p, t) ->
        ( pat_to_string_without_paren p ~depth
          ^ " " ^ ":" ^ " "
          ^ type_to_string_without_paren t ~depth,
          true )

  and pat_to_string_with_paren (x : AST.pat) ~depth : string =
    let s, b = pat_to_string x ~depth in
    if b then "(" ^ s ^ ")" else s

  and pat_to_string_without_paren (x : AST.pat) ~depth : string =
    let s, _ = pat_to_string x ~depth in
    s

  and term_to_string (x : AST.term) ~depth : string * bool =
    match x with
    | Unimplemented x -> ("Unimplemented" ^ " " ^ x, true)
    (* Values *)
    | UnitTerm -> ("tt", false)
    | BoolTerm true -> ("true", false)
    | BoolTerm false -> ("false", false)
    | IntTerm i -> (Int.to_string i, false)
    | RecordTerm (x, l) -> ("TODO RECORD", true)
    | ProductTerm (l, n) ->
        ( "("
          ^ String.concat ~sep:"," (List.map ~f:(term_to_string_without_paren ~depth) l)
          ^ ")" ^ "is" ^ Int.to_string n,
          false )
    | Array l ->
        ( "["
          ^ String.concat ~sep:"," (List.map ~f:(term_to_string_without_paren ~depth) l)
          ^ "]",
          false )
    (* Variables *)
    | Ident x -> (x, false)
    | Let { pattern; value; body; value_typ } ->
        ( "let" ^ " "
          ^ pat_to_string_without_paren pattern ~depth
          ^ " " ^ ":=" ^ " "
          ^ term_to_string_without_paren value ~depth
          ^ " " ^ "in" ^ newline_indent depth
          ^ term_to_string_without_paren body ~depth,
          false )
    | App (x, y) ->
        (term_to_string_with_paren x ~depth ^ " " ^ term_to_string_with_paren y ~depth, true)
    | Set (x, (n, y)) ->
        ( term_to_string_with_paren x ~depth
          ^ "[" ^ n ^ " " ^ ":=" ^ " "
          ^ term_to_string_without_paren y ~depth
          ^ "]",
          false )
    (* Higher order *)
    | Lambda l ->
      ("λ" ^ " " ^
      String.concat ~sep:(newline_indent depth ^ "|" ^ " ")
        (List.map ~f:(function
             | ([], body) ->
               "()" ^ "," ^ " " ^ term_to_string_without_paren body ~depth
             | (args, body) ->
               String.concat ~sep:" " (List.map ~f:(pat_to_string_with_paren ~depth) args)
                 ^ "," ^ newline_indent depth
                 ^ term_to_string_without_paren body ~depth ) l),
                 true)
    | Type ty -> ("TODO TY", true)
    | TypedTerm (term, ty) -> (term_to_string_without_paren term ~depth ^ " " ^ ":" ^ " " ^ type_to_string_without_paren ty ~depth, true)

  and term_to_string_with_paren (x : AST.term) ~depth : string =
    let s, b = term_to_string x ~depth in
    if b then "(" ^ s ^ ")" else s

  and term_to_string_without_paren (x : AST.term) ~depth : string =
    let s, _ = term_to_string x ~depth in
    s

  let rec decl_to_string (x : AST.decl) ~depth : string =
    match x with
    | Unimplemented x -> "(" ^ "Unimplemented" ^ " " ^ x ^ ")"
    | Annotation x -> x
    | Macro (n, args) -> "Macro" ^ " " ^ n ^ "(" ^ String.concat ~sep:"," args ^ ")"
    | Definition (name, value) ->
      "Definition" ^ " " ^ name ^ " " ^ ":="
      ^ newline_indent (depth+1)
      ^ term_to_string_without_paren value ~depth:(depth+1)
    | TypeDefinition (name, typ) ->
      "Type-Definition" ^ " " ^ name ^ " " ^ ":=" ^ " " ^ type_to_string_without_paren typ ~depth:(depth+1)
    | Section (name, decls) ->
        "Section" ^ " " ^ name ^ newline_indent (depth+1)
        ^ String.concat ~sep:(newline_indent (depth+1)) (List.map ~f:(decl_to_string ~depth:(depth+1)) decls)
        ^ newline_indent (depth+1) ^ "End" ^ " " ^ name
    | Import i -> "Import" ^ " " ^ i
end

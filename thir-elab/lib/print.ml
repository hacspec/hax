open Base
open Ast
open PPrint
open Utils

let pmut mut = match mut with Mutable _ -> string "mut" | _ -> empty

let rec pliteral (e : literal) =
  string
  @@
  match e with
  | String s -> "\"" ^ s ^ "\""
  | Char c -> "'" ^ Char.to_string c ^ "'"
  | Int { value } -> Bigint.to_string value
  | Float _ -> "float_todo"
  | Bool b -> string_of_bool b

let rec pglobal_ident (e : global_ident) =
  match e with
  | `Concrete { crate; path } ->
      string crate ^^ string "::"
      ^^ separate_map (string "::") string (Non_empty_list.to_list path)
  | `Primitive p -> string @@ show_primitive_ident p
  | `Tuple n -> string @@ "tuple" ^ string_of_int n
  | `TupleField n -> string @@ "tuple_todo?._" ^ string_of_int n
  | `Projector n -> string @@ show_global_ident e

let rec plocal_ident (e : LocalIdent.t) = string @@ e.name

let rec pty (e : 'a ty) =
  match e with
  | Bool -> string "bool"
  | Char -> string "char"
  | Int k -> string "int"
  | Float -> string "float"
  | Str -> string "str"
  | App { ident; args } ->
      group @@ pglobal_ident ident ^/^ separate_map space pgeneric_arg args
  | Array { typ; length } ->
      string "vector" ^/^ parens (pty typ) ^/^ string (string_of_int length)
  | Slice { witness; ty } -> string "slice:todo"
  | RawPointer { witness } -> string "rawpointer:todo"
  | Ref { witness; region; typ; mut } -> string "&" ^^ pmut mut ^/^ pty typ
  | False -> string "⊥"
  | Param i -> plocal_ident i
  | Arrow (inputs, output) ->
      parens
        (separate_map (space ^^ string "->" ^^ space) pty (inputs @ [ output ]))
  | ProjectedAssociatedType s -> string "proj:assoc:type"

and pgeneric_arg (e : 'a generic_arg) =
  match e with
  | Lifetime _ -> string "todo:lifetime"
  | Type t -> group @@ parens @@ pty t
  | _ -> string "generic_argtodo"

let rec pborrow_kind (e : 'a borrow_kind) =
  match e with Mut _ -> string "mut " | _ -> empty

let rec ppat (e : 'a pat) =
  match e.v with
  | Wild -> underscore
  | PatAscription { typ; pat } ->
      group @@ parens @@ pty typ.v ^/^ colon ^/^ ppat pat
  | Variant { name; args } ->
      group @@ pglobal_ident name ^/^ braces
      @@ separate_map space
           (fun { field; pat } -> pglobal_ident field ^/^ colon ^/^ ppat pat)
           args
  | PatArray { args } -> string "makes no sense"
  | Deref { subpat } -> string "deref" ^/^ ppat subpat
  | Constant { lit } -> pliteral lit
  | Binding { mut; mode; var; typ; subpat } ->
      group
        (pmut mut ^/^ plocal_ident var
        ^/^ optional
              (fun (subpat, _) -> at ^^ group @@ parens @@ ppat subpat)
              subpat)

let rec pexpr (e : 'a expr) =
  match e.v with
  | If { cond; then_; else_ } ->
      group
        (string "if" ^/^ pexpr cond ^/^ string "then" ^/^ pexpr then_
        ^/^ Option.value_map else_ ~default:empty ~f:(fun else_ ->
                string "else" ^/^ pexpr else_))
  | App { f; args } ->
      parens (pexpr f) ^/^ concat @@ List.map ~f:(parens << pexpr) args
  | Literal e -> pliteral e
  | Array l -> brackets @@ separate semi @@ List.map ~f:pexpr l
  | Record { fields; base } ->
      braces
      @@ optional (fun base -> parens (pexpr base) ^^ string "with") base
      ^/^ separate_map semi
            (fun (field, e) -> pglobal_ident field ^^ pexpr e)
            fields
  | Match { scrutinee; arms } ->
      group
        (group (string "match" ^/^ pexpr scrutinee ^/^ string "with")
        ^/^ separate_map hardline parm arms)
  | Let { lhs; rhs; body } -> (
      match lhs.v with
      | Wild -> pexpr rhs ^^ semi ^^ hardline ^^ pexpr body
      | _ ->
          group
            (string "let" ^/^ ppat lhs ^/^ equals ^/^ pexpr rhs ^/^ string "in")
          ^/^ pexpr body)
  | LocalVar local_ident -> plocal_ident local_ident
  | GlobalVar global_ident -> pglobal_ident global_ident
  | Ascription { e; typ } -> group (pexpr e ^/^ string "<:" ^/^ pty typ)
  | MacroInvokation { macro; args } -> string "<macro>"
  | Assign { lhs; e } -> group (plhs lhs ^/^ string ":=" ^/^ pexpr e)
  | Loop { body; label } ->
      group
        (string "loop[" ^^ optional string label ^^ string "]"
       ^/^ string "begin" ^/^ pexpr body ^/^ string "end")
  | Break { e; label } ->
      string "break(" ^^ optional pexpr e ^^ string ")["
      ^^ optional string label ^^ string "]"
  | Return { e } -> string "return(" ^^ optional pexpr e ^^ string ")"
  | Continue { label } ->
      string "continue[" ^^ optional string label ^^ string "]"
  | Borrow { kind; e } -> string "&" ^^ pborrow_kind kind ^^ parens (pexpr e)
  | AddressOf { mut; e } -> string "&raw..."
  | MonadicNode _ -> string "monadic node"

and parm ({ v = { pat; body } } : 'a arm) =
  group (group (group (string "|" ^/^ ppat pat) ^/^ string "->") ^/^ pexpr body)

and plhs (e : 'a lhs) =
  match e with
  | FieldAccessor { e; field } -> pexpr e ^^ dot ^^ string field
  | ArrayAccessor { e; index } -> pexpr e ^^ brackets @@ pexpr index
  | LhsLocalVar i -> plocal_ident i

let rec pparam ({ pat; typ } : 'a param) =
  group @@ parens @@ ppat pat ^/^ colon ^/^ pty typ

let rec pitem (e : 'a item) =
  match e.v with
  | Fn { name; generics; body; params } ->
      group
        (string "let" ^/^ pglobal_ident name
        ^/^ separate_map space pparam params
        ^/^ equals ^/^ pexpr body)
  | NotImplementedYet -> string "NotImplementedYet"

let rec pmutability (e : 'a mutability) = string ""
let rec pbinding_mode (e : 'a binding_mode) = string ""

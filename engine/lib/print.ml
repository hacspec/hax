open Base
open Ast
open Ast.Make (Features.Full)
open PPrint
open Utils

let pmut mut = match mut with Mutable _ -> string "mut" | _ -> empty

let rec pliteral (e : literal) =
  string
  @@
  match e with
  | String s -> "\"" ^ s ^ "\""
  | Char c -> "'" ^ Char.to_string c ^ "'"
  | Int { value } -> value
  | Float _ -> "float_todo"
  | Bool b -> string_of_bool b

let rec pglobal_ident (e : global_ident) =
  match e with
  | `Concrete { crate; path } ->
      string crate ^^ string "::"
      ^^ separate_map (string "::") string (Non_empty_list.to_list path)
  | `Primitive p -> string @@ show_primitive_ident p
  | `TupleType n -> string @@ "tuple" ^ string_of_int n
  | `TupleCons n -> string @@ "Tuple" ^ string_of_int n
  | `TupleField (n, _) -> string @@ "tuple_todo?._" ^ string_of_int n
  | `Projector n -> string @@ show_global_ident e

let rec plocal_ident (e : LocalIdent.t) = string @@ e.name

let rec pty (e : ty) =
  match e with
  | TBool -> string "bool"
  | TChar -> string "char"
  | TInt k -> string "int"
  | TFloat -> string "float"
  | TStr -> string "str"
  | TApp { ident; args } ->
      group @@ pglobal_ident ident ^/^ separate_map space pgeneric_value args
  | TArray { typ; length } ->
      string "vector" ^/^ parens (pty typ) ^/^ string (string_of_int length)
  | TSlice { witness; ty } -> string "slice:todo"
  | TRawPointer { witness } -> string "rawpointer:todo"
  | TRef { witness; region; typ; mut } -> string "&" ^^ pmut mut ^/^ pty typ
  | TFalse -> string "⊥"
  | TParam i -> plocal_ident i
  | TArrow (inputs, output) ->
      parens
        (separate_map (space ^^ string "->" ^^ space) pty (inputs @ [ output ]))
  | TProjectedAssociatedType s -> string "proj:assoc:type"

and pgeneric_value (e : generic_value) =
  match e with
  | GLifetime _ -> string "todo:lifetime"
  | GType t -> group @@ parens @@ pty t
  | _ -> string "generic_value todo"

let rec pborrow_kind (e : borrow_kind) =
  match e with Mut _ -> string "mut " | _ -> empty

let rec ppat (e : pat) =
  match e.p with
  | PWild -> underscore
  | PAscription { typ; pat } ->
      group @@ parens @@ pty typ ^/^ colon ^/^ ppat pat
  | PConstruct { name; args } ->
      group @@ pglobal_ident name ^/^ braces
      @@ separate_map space
           (fun { field; pat } -> pglobal_ident field ^/^ colon ^/^ ppat pat)
           args
  | PArray { args } -> string "makes no sense"
  | PDeref { subpat } -> string "deref" ^/^ ppat subpat
  | PConstant { lit } -> pliteral lit
  | PBinding { mut; mode; var; typ; subpat } ->
      group
        (pmut mut ^/^ plocal_ident var
        ^/^ optional
              (fun (subpat, _) -> at ^^ group @@ parens @@ ppat subpat)
              subpat)

let rec pexpr (e : expr) =
  match e.e with
  | If { cond; then_; else_ } ->
      group
        (string "if" ^/^ pexpr cond ^/^ string "then" ^/^ pexpr then_
        ^/^ Option.value_map else_ ~default:empty ~f:(fun else_ ->
                string "else" ^/^ pexpr else_))
  | App { f; args } ->
      parens (pexpr f) ^/^ concat @@ List.map ~f:(parens << pexpr) args
  | Literal e -> pliteral e
  | Array l -> brackets @@ separate semi @@ List.map ~f:pexpr l
  | Construct { constructor; constructs_record; fields; base } ->
      braces
      @@ optional (fun base -> parens (pexpr base) ^^ string "with") base
      ^/^ separate_map semi
            (fun (field, e) -> pglobal_ident field ^^ pexpr e)
            fields
  | Match { scrutinee; arms } ->
      group
        (group (string "match" ^/^ pexpr scrutinee ^/^ string "with")
        ^/^ separate_map hardline parm arms)
  | Let { monadic = Some _; lhs; rhs; body } -> string "monadic Let"
  | Let { monadic = _; lhs; rhs; body } -> (
      match lhs.p with
      | PWild -> pexpr rhs ^^ semi ^^ hardline ^^ pexpr body
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
      string "break(" ^^ pexpr e ^^ string ")[" ^^ optional string label
      ^^ string "]"
  | Return { e } -> string "return(" ^^ pexpr e ^^ string ")"
  | Continue { label } ->
      string "continue[" ^^ optional string label ^^ string "]"
  | Borrow { kind; e } -> string "&" ^^ pborrow_kind kind ^^ parens (pexpr e)
  | AddressOf { mut; e } -> string "&raw..."
  | MonadicAction _ -> string "monadic action"
  | Closure { params; body } -> string "closure"
  | ForLoop _ -> string "ForLoop"

and parm { arm = { pat; body } } =
  group (group (group (string "|" ^/^ ppat pat) ^/^ string "->") ^/^ pexpr body)

and plhs (e : lhs) =
  match e with
  | LhsFieldAccessor { e; field; _ } -> plhs e ^^ dot ^^ string field
  | LhsArrayAccessor { e; index; _ } -> plhs e ^^ brackets @@ pexpr index
  | LhsLocalVar { var; _ } -> plocal_ident var
  | LhsArbitraryExpr { e; _ } -> pexpr e

let rec pparam ({ pat; typ } : param) =
  group @@ parens @@ ppat pat ^/^ colon ^/^ pty typ

let rec pitem (e : item) =
  match e.v with
  | Fn { name; generics; body; params } ->
      group
        (string "let" ^/^ pglobal_ident name
        ^/^ separate_map space pparam params
        ^/^ equals ^/^ pexpr body)
  | Type { name; generics; variants } -> string "TYPEDEF"
  | TyAlias { name; generics; ty } -> string "TYPEALIAS"
  | NotImplementedYet -> string "NotImplementedYet"
  | IMacroInvokation _ -> string "MacroInvok"
  | _ -> string "pitem: TODO"

let rec pmutability (e : 'a mutability) = string ""
let rec pbinding_mode (e : binding_mode) = string ""

let to_string d =
  let b = Buffer.create 50 in
  PPrint.ToBuffer.pretty 0.5 140 b d;
  Buffer.contents b

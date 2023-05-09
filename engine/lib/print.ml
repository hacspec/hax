open Base
open Ast
open Ast.Make (Features.Full)
open PPrint
open Utils

let pmut mut = match mut with Mutable _ -> string "mut" | _ -> empty

let pliteral (e : literal) =
  string
  @@
  match e with
  | String s -> "\"" ^ s ^ "\""
  | Char c -> "'" ^ Char.to_string c ^ "'"
  | Int { value; _ } -> value
  | Float _ -> "float_todo"
  | Bool b -> Bool.to_string b

let pglobal_ident (e : global_ident) =
  match e with
  | `Concrete { crate; path } ->
      string crate ^^ string "::"
      ^^ separate_map (string "::") string (Non_empty_list.to_list path)
  | `Primitive p -> string @@ show_primitive_ident p
  | `TupleType n -> string @@ "tuple" ^ Int.to_string n
  | `TupleCons n -> string @@ "Tuple" ^ Int.to_string n
  | `TupleField (n, _) -> string @@ "tuple_todo?._" ^ Int.to_string n
  | `Projector _n -> string @@ show_global_ident e

let plocal_ident (e : LocalIdent.t) = string @@ e.name

let rec pty (e : ty) =
  match e with
  | TBool -> string "bool"
  | TChar -> string "char"
  | TInt _k -> string "int"
  | TFloat -> string "float"
  | TStr -> string "str"
  | TApp { ident; args } ->
      group @@ pglobal_ident ident ^/^ separate_map space pgeneric_value args
  | TArray { typ; length } ->
      string "vector" ^/^ parens (pty typ) ^/^ string (Int.to_string length)
  | TSlice _ -> string "slice:todo"
  | TRawPointer _ -> string "rawpointer:todo"
  | TRef { typ; mut; _ } -> string "&" ^^ pmut mut ^/^ pty typ
  | TFalse -> string "⊥"
  | TParam i -> plocal_ident i
  | TArrow (inputs, output) ->
      parens
        (separate_map (space ^^ string "->" ^^ space) pty (inputs @ [ output ]))
  | TProjectedAssociatedType _ -> string "proj:assoc:type"

and pgeneric_value (e : generic_value) =
  match e with
  | GLifetime _ -> string "todo:lifetime"
  | GType t -> group @@ parens @@ pty t
  | _ -> string "generic_value todo"

let pborrow_kind (e : borrow_kind) =
  match e with Mut _ -> string "mut " | _ -> empty

let rec ppat (e : pat) =
  match e.p with
  | PWild -> underscore
  | PAscription { typ; pat; _ } ->
      group @@ parens @@ pty typ ^/^ colon ^/^ ppat pat
  | PConstruct { name; args; _ } ->
      group @@ pglobal_ident name ^/^ braces
      @@ separate_map space
           (fun { field; pat } -> pglobal_ident field ^/^ colon ^/^ ppat pat)
           args
  | PArray _ -> string "makes no sense"
  | PDeref { subpat; _ } -> string "deref" ^/^ ppat subpat
  | PConstant { lit } -> pliteral lit
  | PBinding { mut; var; subpat; _ } ->
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
  | Construct { fields; base; _ } ->
      braces
      @@ optional (fun base -> parens (pexpr base) ^^ string "with") base
      ^/^ separate_map semi
            (fun (field, e) -> pglobal_ident field ^^ pexpr e)
            fields
  | Match { scrutinee; arms } ->
      group
        (group (string "match" ^/^ pexpr scrutinee ^/^ string "with")
        ^/^ separate_map hardline parm arms)
  | Let { monadic = Some _; _ } -> string "monadic Let"
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
  | MacroInvokation _ -> string "<macro>"
  | Assign { lhs; e; _ } -> group (plhs lhs ^/^ string ":=" ^/^ pexpr e)
  | Loop { body; label; _ } ->
      group
        (string "loop[" ^^ optional string label ^^ string "]"
       ^/^ string "begin" ^/^ pexpr body ^/^ string "end")
  | Break { e; label; _ } ->
      string "break(" ^^ pexpr e ^^ string ")[" ^^ optional string label
      ^^ string "]"
  | Return { e; _ } -> string "return(" ^^ pexpr e ^^ string ")"
  | Continue { label; _ } ->
      string "continue[" ^^ optional string label ^^ string "]"
  | Borrow { kind; e; _ } -> string "&" ^^ pborrow_kind kind ^^ parens (pexpr e)
  | AddressOf _ -> string "&raw..."
  | EffectAction _ -> string "EffectAction"
  | Closure _ -> string "closure"
(* | ForLoop _ -> string "ForLoop" *)

and parm { arm = { pat; body; _ }; _ } =
  group (group (group (string "|" ^/^ ppat pat) ^/^ string "->") ^/^ pexpr body)

and plhs (e : lhs) =
  match e with
  | LhsFieldAccessor { e; field; _ } -> plhs e ^^ dot ^^ string field
  | LhsArrayAccessor { e; index; _ } -> plhs e ^^ brackets @@ pexpr index
  | LhsLocalVar { var; _ } -> plocal_ident var
  | LhsArbitraryExpr { e; _ } -> pexpr e

let pparam ({ pat; typ; _ } : param) =
  group @@ parens @@ ppat pat ^/^ colon ^/^ pty typ

let pitem (e : item) =
  match e.v with
  | Fn { name; body; params; _ } ->
      group
        (string "let" ^/^ pglobal_ident name
        ^/^ separate_map space pparam params
        ^/^ equals ^/^ pexpr body)
  | Type _ -> string "TYPEDEF"
  | TyAlias _ -> string "TYPEALIAS"
  | NotImplementedYet -> string "NotImplementedYet"
  | IMacroInvokation _ -> string "MacroInvok"
  | _ -> string "pitem: TODO"

let pmutability (_e : 'a mutability) = string ""
let pbinding_mode (_e : binding_mode) = string ""

let to_string d =
  let b = Buffer.create 50 in
  PPrint.ToBuffer.pretty 0.5 140 b d;
  Buffer.contents b

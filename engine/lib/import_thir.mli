type error =
  | UnsafeBlock
  | LetElse
  | LetWithoutInit
  | GotErrLiteral
  | BadSpanUnion
  | ShallowMutUnsupported
  | GotTypeInLitPat
  | IllTypedIntLiteral
[@@deriving show]

val c_item :
  Types.item_for__decorated_for__expr_kind ->
  (Ast.Rust.item list, error) Result.t

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

val c_item : Types.item -> (Ast.Rust.item list, error) Result.t

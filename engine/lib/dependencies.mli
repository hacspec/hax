module Make (F : Features.T) : sig
  module AST : module type of Ast.Make (F)

  val uid_associated_items : AST.item list -> Ast.attrs -> AST.item list
  val name_me : AST.item list -> AST.item list
  val sort : AST.item list -> AST.item list
  val recursive_bundles : AST.item list -> AST.item list list * AST.item list

  val filter_by_inclusion_clauses :
    Types.inclusion_clause list -> AST.item list -> AST.item list
end

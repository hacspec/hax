module Make (F : Features.T) : sig
  module AST : module type of Ast.Make (F)

  val name_me : AST.item list -> AST.item list
  val sort : AST.item list -> AST.item list

  val filter_by_inclusion_clauses :
    Types.inclusion_clause list -> AST.item list -> AST.item list
end

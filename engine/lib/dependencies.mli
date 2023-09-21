module Make (F : Features.T): sig
      module AST: module type of Ast.Make (F)
      module ItemGraph: sig
          val transitive_dependencies_of_items : Concrete_ident.t list -> AST.item list -> AST.item list
        end
      val name_me: AST.item list -> AST.item list
end

open Base
open Ast

module type T = sig
  module InputLanguage : Features.T
  module AST : Ast.T

  module U : sig
    module Mappers : sig
      val rename_global_idents_item :
        (Ast_utils.visit_level -> global_ident -> global_ident) ->
        AST.item ->
        AST.item
    end
  end

  module BackendOptions : sig
    type t
  end

  val apply_phases : BackendOptions.t -> Ast.Rust.item -> AST.item list
  val translate : BackendOptions.t -> AST.item list -> Raw_thir_ast.output
  val name : string
end

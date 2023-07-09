open Base
open Utils

module%inlined_contents Make (F : Features.T) = struct
  module FA = F
  module A = Ast.Make (F)
  module U = Ast_utils.Make (F)
  open Ast

  let rec flatten_ast : A.expr -> A.expr list =
    (object
       inherit [_] A.expr_reduce as super
       inherit [_] U.Reducers.expr_list_monoid as m
       method visit_t _ _ = m#zero
       method visit_mutability (_f : unit -> _ -> _) () _ = m#zero
       method visit_expr f e = e :: super#visit_expr f e
    end)
      #visit_expr
      ()
end

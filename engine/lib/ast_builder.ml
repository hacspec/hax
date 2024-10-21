open! Prelude
open! Ast

module Make (F : Features.T) = struct
  module AST = Ast.Make (F)
  open AST

  open struct
    module Gen = Ast_builder_generated.Make (F)
  end

  module type SPAN = Gen.SPAN

  include Gen.Explicit

  module NoSpan = struct
    let ty_tuple (types : ty list) : ty =
      let ident = `TupleType (List.length types) in
      let args = List.map ~f:(fun typ -> GType typ) types in
      TApp { ident; args }

    let ty_tuple_or_id : ty list -> ty = function
      | [ ty ] -> ty
      | types -> ty_tuple types
  end

  include NoSpan

  module Explicit = struct
    let ty_unit : ty = TApp { ident = `TupleType 0; args = [] }
    let expr_unit = expr_GlobalVar (`TupleCons 0) ~typ:ty_unit
    let pat_PBinding ~typ = pat_PBinding ~inner_typ:typ ~typ

    let arm ~span arm_pat ?(guard = None) body =
      { arm = { arm_pat; body; guard }; span }
  end

  include Explicit

  module Make0 (Span : Gen.SPAN) = struct
    open! Span
    include Gen.Make (Span)
    include NoSpan

    let pat_PBinding = Explicit.pat_PBinding ~span
    let expr_unit = expr_unit ~span
    let arm ?(guard = None) = arm ~span ?guard
  end

  module type S = module type of Make0 (struct
    let span = failwith "dummy"
  end)

  module Make (Span : sig
    val span : span
  end) : S =
    Make0 (Span)

  let make : span -> (module S) =
   fun span : (module S) ->
    (module Make0 (struct
      let span = span
    end))
end

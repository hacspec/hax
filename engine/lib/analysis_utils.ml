open Base

module type ANALYSIS = sig
  (* module FA : Features.T *)
  module A : Ast.T

  type analysis_data
  type pre_data

  val analyse : pre_data -> A.item list -> analysis_data
end

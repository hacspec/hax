open Base

module type ANALYSIS = sig
  (* module FA : Features.T *)
  module A : Ast.T

  type pre_data
  type analysis_data

  val analyse : pre_data -> A.item list -> analysis_data
end

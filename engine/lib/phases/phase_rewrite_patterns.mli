(** This phase rewrites patterns that don't need a guard in Rust 
    but need one in a backend. Currently it rewrites array/slice 
    patterns and usize/isize, u128/i128 patterns. *)

module Make
    (F : Features.T
           with type match_guard = Features.On.match_guard
            and type slice = Features.On.slice
            and type reference = Features.On.reference) : sig
  include module type of struct
    module FB = F
    module A = Ast.Make (F)
    module B = Ast.Make (FB)
    module ImplemT = Phase_utils.MakePhaseImplemT (A) (B)
    module FA = F
  end

  include ImplemT.T
end

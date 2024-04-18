(** This phase transforms nodes like:
    {@rust[
    hax_lib::inline({
      let _KIND = ...;
      ...
      let _KIND = ...;
      "payload"
    })
    ]}

    into [hax_lib::inline("payload'")] where [payload'] is a string
    with all the binding names substituted.

    Note: above `_KIND` can be `_expr`, `_pat` or `_constructor`.
*)

module Make (F : Features.T) : sig
  include module type of struct
    module FB = struct
      include F
      include Features.On.Quote
    end

    module A = Ast.Make (F)
    module B = Ast.Make (FB)
    module ImplemT = Phase_utils.MakePhaseImplemT (A) (B)
    module FA = F
  end

  include ImplemT.T
end

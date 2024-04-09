(** In THIR, there are no construct for question marks. Instead, Rustc
desugars `e?` into the following:

{@rust[
match core::ops::try_trait::branch(y) {
    core::ops::control_flow::Break(residual) => {
        never_to_any(
            {return core::ops::try_trait::from_residual(residual)},
        )
    }
    core::ops::control_flow::Continue(val) => val,
})
]}

This phase does the opposite rewrite.

While `e?` in Rust might implies an implicit coercion, in our AST, a
question mark is expected to already be of the right type. This phase
inlines a coercion (of the shape `x.map_err(from)`, in the case of a
`Result`).

*)

module Make (F : Features.T) : sig
  include module type of struct
    module FA = F

    (** This phase outputs an AST with question marks. *)
    module FB = struct
      include F
      include Features.On.Question_mark
    end

    module A = Ast.Make (F)
    module B = Ast.Make (FB)
    module ImplemT = Phase_utils.MakePhaseImplemT (A) (B)
  end

  include ImplemT.T
end

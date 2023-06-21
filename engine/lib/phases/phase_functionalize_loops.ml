open Base
open Utils

module%inlined_contents Make
    (F : Features.T
           with type continue = Features.Off.continue
            and type early_exit = Features.Off.early_exit) =
struct
  open Ast
  module FA = F

  module FB = struct
    include F
    include Features.Off.Loop
    include Features.Off.For_loop
    include Features.Off.For_index_loop
    include Features.Off.State_passing_loop
  end

  include
    Phase_utils.MakeBase (F) (FB)
      (struct
        let phase_id = Diagnostics.Phase.FunctionalizeLoops
      end)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module UA = Ast_utils.Make (F)
    module UB = Ast_utils.Make (FB)

    module S = struct
      include Features.SUBTYPE.Id
    end

    [%%inline_defs dmutability]

    let rec dexpr_unwrapped (expr : A.expr) : B.expr =
      let span = expr.span in
      match expr.e with
      | Loop
          {
            body;
            kind = ForLoop { it; pat; _ };
            state = Some { init; bpat; _ };
            _;
          } ->
          let body = dexpr body in
          let it = dexpr it in
          let pat = dpat pat in
          let bpat = dpat bpat in
          let fn : B.expr' =
            Closure { params = [ bpat; pat ]; body; captures = [] }
          in
          let fn : B.expr =
            {
              e = fn;
              typ = TArrow ([ bpat.typ; pat.typ ], body.typ);
              span = body.span;
            }
          in
          UB.call Core__iter__traits__iterator__Iterator__fold
            [ it; dexpr init; fn ]
            span (dty span expr.typ)
      | Loop { state = None; _ } ->
          Error.unimplemented ~details:"Loop without mutation?" span
      | Loop _ ->
          Error.unimplemented
            ~details:"Only for loop are being functionalized for now" span
      | Break _ ->
          Error.unimplemented
            ~details:
              "For now, the AST node [Break] is feature gated only by [loop], \
               there is nothing for having loops but no breaks."
            span
      | [%inline_arms "dexpr'.*" - Loop - Break - Continue - Return] ->
          map (fun e -> B.{ e; typ = dty expr.span expr.typ; span = expr.span })
      | _ -> .
      [@@inline_ands bindings_of dexpr - dexpr' - dloop_kind - dloop_state]

    [%%inline_defs "Item.*"]
  end

  include Implem
end
[@@add "subtype.ml"]

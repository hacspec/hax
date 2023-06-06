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

    [%%inline_defs dmutability + dty + dborrow_kind + dpat + dsupported_monads]

    let rec dexpr = [%inline_body dexpr]

    and dexpr_unwrapped (expr : A.expr) : B.expr =
      let span = expr.span in
      match expr.e with
      | Loop
          {
            body;
            kind = ForLoop { start; end_; var; var_typ; _ };
            state = Some { init; bpat; _ };
            _;
          } ->
          let body = dexpr body in
          let var_typ = dty span var_typ in
          let bpat = dpat bpat in
          let fn : B.expr' =
            Closure
              {
                params = [ UB.make_var_pat var var_typ span; bpat ];
                body;
                captures = [];
              }
          in
          let fn : B.expr =
            {
              e = fn;
              typ = TArrow ([ var_typ; bpat.typ ], body.typ);
              span = body.span;
            }
          in
          UB.call "dummy" "foldi" []
            [ dexpr start; dexpr end_; fn; dexpr init ]
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

    and dloop_kind = [%inline_body dloop_kind]
    and dloop_state = [%inline_body dloop_state]
    and darm = [%inline_body darm]
    and darm' = [%inline_body darm']
    and dlhs = [%inline_body dlhs]

    [%%inline_defs "Item.*"]
  end

  include Implem
end
[@@add "subtype.ml"]

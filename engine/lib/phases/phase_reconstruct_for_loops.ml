open Base
open Utils

module%inlined_contents Make
    (FA : Features.T
    (* with type raw_pointer = Features.off *)
    (*  and type mutable_pointer = Features.off *)) =
struct
  open Ast

  module FB = struct
    include FA
    include Features.On.For_loop
  end

  include
    Phase_utils.MakeBase (FA) (FB)
      (struct
        let phase_id = Diagnostics.Phase.ResugarForLoops
      end)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module UA = Ast_utils.Make (FA)
    module UB = Ast_utils.Make (FB)

    module S = struct
      include Features.SUBTYPE.Id

      let for_loop = Fn.const Features.On.for_loop
    end

    module For = struct
      [@@@warning "-9"]

      open A

      type t = {
        it : expr;
        pat : pat;
        body : expr;
        state : loop_state option;
        label : string option;
        witness : FA.loop;
      }
      [@@deriving show]

      let extract_loop_body (e : expr) =
        match e.e with
        | Match
            {
              scrutinee =
                {
                  e =
                    App
                      {
                        f = { e = GlobalVar (`Concrete next) };
                        args =
                          [
                            {
                              e =
                                Borrow { kind = Mut _; e = { e = LocalVar v } };
                            };
                          ];
                      };
                };
              arms =
                [
                  {
                    arm =
                      {
                        arm_pat =
                          {
                            p =
                              PConstruct { name = `Concrete none; args = []; _ };
                          };
                        body =
                          { e = Break { e = { e = GlobalVar (`TupleCons 0) } } };
                      };
                  };
                  {
                    arm =
                      {
                        arm_pat =
                          {
                            p =
                              PConstruct
                                { name = `Concrete some; args = [ { pat } ]; _ };
                          };
                        body =
                          ( {
                              e =
                                Let
                                  {
                                    lhs = { p = PWild };
                                    rhs = body;
                                    body = { e = GlobalVar (`TupleCons 0) };
                                  };
                            }
                          | body );
                      };
                  };
                ];
            }
          when Concrete_ident.eq_name
                 Core__iter__traits__iterator__Iterator__next next
               && Concrete_ident.eq_name Core__option__Option__None none
               && Concrete_ident.eq_name Core__option__Option__Some some ->
            Some (v, pat, body)
        | _ -> None

      let extract (e : expr) : t option =
        let e = UA.Mappers.normalize_borrow_mut#visit_expr () e in
        match e.e with
        | Match
            {
              scrutinee = it;
              arms =
                [
                  {
                    arm =
                      {
                        arm_pat =
                          {
                            p =
                              PBinding
                                {
                                  mut = Mutable _;
                                  mode = ByValue;
                                  var = iter_variable;
                                  subpat = None;
                                };
                          };
                        body =
                          {
                            e =
                              Loop
                                {
                                  label;
                                  kind = UnconditionalLoop;
                                  state;
                                  witness;
                                  body =
                                    ( {
                                        e =
                                          Let
                                            {
                                              monadic = None;
                                              lhs = { p = PWild };
                                              rhs = loop_body;
                                              body =
                                                { e = GlobalVar (`TupleCons 0) };
                                            };
                                      }
                                    | loop_body );
                                  _;
                                };
                          };
                      };
                  };
                ];
            } -> (
            match extract_loop_body loop_body with
            | Some (next_iter_variable, pat, body)
              when [%eq: local_ident] iter_variable next_iter_variable ->
                Some { it; pat; body; state; label; witness }
            | _ -> None)
        | _ -> None
               [@ocamlformat "disable"]
    end

    [%%inline_defs dmutability]

    let rec dexpr_unwrapped (expr : A.expr) : B.expr =
      let h = [%inline_body dexpr_unwrapped] in
      match For.extract expr with
      | Some { it; pat; body; label; state; witness } ->
          {
            e =
              Loop
                {
                  body = dexpr body;
                  kind =
                    ForLoop
                      {
                        it = dexpr it;
                        pat = dpat pat;
                        witness = Features.On.for_loop;
                      };
                  state = Option.map ~f:(dloop_state expr.span) state;
                  label;
                  witness = S.loop witness;
                };
            span = expr.span;
            typ = UB.unit_typ;
          }
      | None -> h expr
      [@@inline_ands bindings_of dexpr]

    [%%inline_defs "Item.*"]
  end

  include Implem
  module FA = FA
end
[@@add "subtype.ml"]

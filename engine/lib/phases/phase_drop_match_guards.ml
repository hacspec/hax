(* This phase removes guards from pattern matchings. It rewrites
   them using only pattern matchings without guards.
   See #806 and the example in tests/guards. *)

(* Rewrite example: *)
(*
    match x {
        None => 0,
        Some(v) if let Ok(y) = v => y,
        Some(Err(y)) => y,
        _ => 1,
    }
*)
(* Becomes *)
(*
    match x {
        None => 0,
        _ => match match x {
            Some(v) => match v {
                Ok(y) => Some(y),
                _ => None,
            },
            _ => None,
        } {
            Some(y) => y,
            None => match x {
                Some(Err(y)) => y,
                _ => 1,
            },
        },
    }
*)

open! Prelude

module%inlined_contents Make (F : Features.T) = struct
  open Ast
  module FA = F

  module FB = struct
    include F
    include Features.Off.Match_guard
  end

  include
    Phase_utils.MakeBase (F) (FB)
      (struct
        let phase_id = Diagnostics.Phase.DropMatchGuards
      end)

  module UA = Ast_utils.Make (F)
  module UB = Ast_utils.Make (FB)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module S = struct
      include Features.SUBTYPE.Id
    end

    [%%inline_defs dmutability + dsafety_kind]

    let maybe_simplified_match scrutinee ?(original_arms : A.arm list = [])
        (arms : B.arm list) : B.expr' =
      match (original_arms, arms) with
      (* If the one wildcard branch was not produced by this phase, keep it *)
      | ( [ { arm = { arm_pat = { p = PWild; _ }; _ }; _ } ],
          [ { arm = { arm_pat = { p = PWild; _ }; _ }; _ } ] ) ->
          Match { scrutinee; arms }
      (* If there is only one wildcard branch we can simplify *)
      | _, [ { arm = { body; arm_pat = { p = PWild; _ }; _ }; _ } ] -> body.e
      (* General case *)
      | _ -> Match { scrutinee; arms }

    let rec dexpr' (span : span) (expr : A.expr') : B.expr' =
      match expr with
      | [%inline_arms "dexpr'.*" - Match] -> auto
      | Match { scrutinee; arms } ->
          let new_arms = transform_arms (dexpr scrutinee) (List.rev arms) [] in
          maybe_simplified_match ~original_arms:arms (dexpr scrutinee) new_arms

    and transform_arms (scrutinee : B.expr) (remaining : A.arm list)
        (treated : B.arm list) : B.arm list =
      match remaining with
      | [] -> treated
      | { arm = { arm_pat; body; guard = None }; span } :: remaining ->
          let new_arm : B.arm = UB.make_arm (dpat arm_pat) (dexpr body) span in
          transform_arms scrutinee remaining (new_arm :: treated)
      (* Matches an arm `arm_pat if let lhs = rhs => body` *)
      (* And rewrites to `_ => match <option_match> {Some(x) => x, None => match scrutinee {<treated>} }` *)
      (* where `option_match` is `match scrutinee {arm_pat => <match_guard>, _ => None }` *)
      (* and `match_guard` is `match rhs {lhs  => Some(body), _ => None}` *)
      (* and `treated` is the other arms coming after this one (that have already been treated as the arms are reversed ) *)
      | {
          arm =
            {
              arm_pat;
              body;
              guard = Some { guard = IfLet { lhs; rhs; _ }; span = guard_span };
            };
          span;
        }
        :: remaining ->
          let result_type = dty span body.typ in
          let opt_result_type = UB.make_opt_type result_type in

          let expr_none = UB.make_opt_expr None guard_span result_type in

          (* This is the nested pattern matching equivalent to the guard *)
          (* Example: .. if let pat = rhs => body *)
          (* Rewrites with match rhs { pat => Some(body), _ => None }*)
          let guard_match : B.expr' =
            Match
              {
                scrutinee = dexpr rhs;
                arms =
                  [
                    UB.make_arm (dpat lhs)
                      (UB.make_opt_expr
                         (Some (dexpr body))
                         guard_span result_type)
                      span;
                    UB.make_arm
                      (UB.make_wild_pat (dty guard_span lhs.typ) guard_span)
                      expr_none guard_span;
                  ];
              }
          in

          (* `r` corresponds to `option_match` in the example above *)
          let r : B.expr =
            {
              e =
                Match
                  {
                    scrutinee;
                    arms =
                      [
                        UB.make_arm (dpat arm_pat)
                          {
                            e = guard_match;
                            span = guard_span;
                            typ = opt_result_type;
                          }
                          guard_span;
                        UB.make_arm
                          (UB.make_wild_pat
                             (dty guard_span arm_pat.typ)
                             guard_span)
                          expr_none guard_span;
                      ];
                  };
              span = guard_span;
              typ = opt_result_type;
            }
          in
          let id = UB.fresh_local_ident_in [] "x" in
          let new_body : B.expr =
            {
              e =
                Match
                  {
                    scrutinee = r;
                    arms =
                      [
                        UB.make_arm
                          (UB.make_opt_pattern
                             (Some
                                {
                                  p =
                                    PBinding
                                      {
                                        mut = Immutable;
                                        mode = ByValue;
                                        var = id;
                                        typ = result_type;
                                        subpat = None;
                                      };
                                  span;
                                  typ = result_type;
                                })
                             guard_span result_type)
                          { e = LocalVar id; span; typ = result_type }
                          guard_span;
                        UB.make_arm
                          (UB.make_opt_pattern None guard_span result_type)
                          {
                            e = maybe_simplified_match scrutinee treated;
                            span = guard_span;
                            typ = result_type;
                          }
                          guard_span;
                      ];
                  };
              span = guard_span;
              typ = result_type;
            }
          in
          let new_arm : B.arm =
            UB.make_arm
              (UB.make_wild_pat (dty span arm_pat.typ) span)
              new_body span
          in
          transform_arms scrutinee remaining [ new_arm ]
      [@@inline_ands
        bindings_of dexpr - dexpr' - darm - darm' - dguard - dguard']

    [%%inline_defs "Item.*"]
  end

  include Implem
end
[@@add "subtype.ml"]

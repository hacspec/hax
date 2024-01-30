(* TODO: handle Exn report *)
open! Prelude
open Side_effect_utils

module%inlined_contents Make
    (F : Features.T
           with type mutable_reference = Features.Off.mutable_reference
            and type mutable_pointer = Features.Off.mutable_pointer
            and type raw_pointer = Features.Off.raw_pointer
            and type arbitrary_lhs = Features.Off.arbitrary_lhs
            and type nontrivial_lhs = Features.Off.nontrivial_lhs
            and type monadic_action = Features.Off.monadic_action
            and type monadic_binding = Features.Off.monadic_binding
            and type for_index_loop = Features.Off.for_index_loop) =
struct
  open Ast
  module FA = F

  module FB = struct
    include F
    (* include Features.Off.Mutable_variable *)
    include Features.On.State_passing_loop
  end

  include
    Phase_utils.MakeBase (F) (FB)
      (struct
        let phase_id = Diagnostics.Phase.LocalMutation
      end)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module UA = Ast_utils.Make (F)
    module UB = Ast_utils.Make (FB)

    module S = struct
      include Features.SUBTYPE.Id
      include Features.SUBTYPE.On.State_passing_loop
    end

    module SI = MakeSI (FB)

    module Instructions = struct
      type t = {
        expr_level : UB.TypedLocalIdent.t list;
        fun_level : UB.TypedLocalIdent.t list;
        loop_level : UB.TypedLocalIdent.t list;
        drop_expr : bool;
      }

      let zero =
        { expr_level = []; fun_level = []; loop_level = []; drop_expr = false }
    end

    let free_assigned_variables =
      UA.Reducers.free_assigned_variables (function _ -> .)

    [%%inline_defs dmutability]

    let rec dpat' (span : span) (p : A.pat') : B.pat' =
      match p with
      | [%inline_arms "dpat'.*" - PBinding - PDeref] -> auto
      | PBinding { var : Local_ident.t; typ; mut; subpat; _ } ->
          PBinding
            {
              mut;
              mode = ByValue;
              var;
              typ = dty span typ;
              subpat = Option.map ~f:(dpat *** Fn.id) subpat;
            }
      | PDeref { subpat; _ } -> (dpat subpat).p

    (* [s] is the list of variables the last expression should return, packed in a tuple *)
    and dexpr_s (s : Instructions.t) (expr : A.expr) : B.expr =
      let dexpr_same e = dexpr_s s e in
      let rec dexpr e = dexpr_s { s with expr_level = []; drop_expr = false } e
      and dloop_state = [%inline_body dloop_state] in
      let span = expr.span in
      match expr.e with
      | Let
          {
            monadic = None;
            lhs;
            rhs =
              {
                e =
                  Assign
                    { lhs = LhsLocalVar { var; typ }; e = value; witness = _ };
                _;
              };
            body;
          } ->
          let h (type a) (f : a list -> a) (x : a) (y : a) =
            match lhs.p with PWild -> y | _ -> f [ x; y ]
          in
          let body = dexpr_same body in
          {
            e =
              Let
                {
                  monadic = None;
                  lhs =
                    h UB.make_tuple_pat (dpat lhs)
                      (UB.make_var_pat var (dty span typ) span);
                  rhs =
                    h (UB.make_tuple_expr ~span) (UB.unit_expr span)
                      (dexpr_s
                         { s with expr_level = []; drop_expr = false }
                         value);
                  body;
                };
            typ = body.typ;
            span = expr.span;
          }
      | Let { monadic = Some _; _ } -> .
      | Let { monadic = None; lhs; rhs; body } ->
          let drop_expr = [%matches? A.PWild] lhs.p in
          let rhs_vars =
            free_assigned_variables#visit_expr () rhs
            |> Set.to_list
            |> List.map ~f:(fun (i, t) -> (i, dty span t))
          in
          let vars_pat =
            List.map ~f:(fun (i, t) -> UB.make_var_pat i t span) rhs_vars
            |> UB.make_tuple_pat
          in
          let lhs = dpat lhs in
          let lhs' =
            if List.is_empty rhs_vars then lhs
            else if drop_expr then vars_pat
            else UB.make_tuple_pat [ vars_pat; lhs ]
          in
          let body = dexpr_same body in
          {
            e =
              Let
                {
                  monadic = None;
                  lhs = lhs';
                  rhs = dexpr_s { s with expr_level = rhs_vars; drop_expr } rhs;
                  body;
                };
            typ = body.typ;
            span = expr.span;
          }
      | Assign { e; lhs = LhsLocalVar { var; _ }; _ } ->
          let vars =
            List.map
              ~f:(fun (i, typ) : B.expr ->
                if Local_ident.equal i var then
                  dexpr_s { s with expr_level = []; drop_expr = false } e
                else { e = LocalVar i; typ; span })
              s.expr_level
          in
          let vars =
            match vars with [ v ] -> v | _ -> UB.make_tuple_expr ~span vars
          in
          if s.drop_expr then vars
          else UB.make_tuple_expr ~span [ vars; UB.unit_expr span ]
      | Assign _ -> .
      | Closure { params; body; captures } ->
          let observable_mutations =
            free_assigned_variables#visit_expr () expr
          in
          if observable_mutations |> Set.is_empty |> not then
            Error.raise
              {
                kind =
                  ClosureMutatesParentBindings
                    {
                      bindings =
                        Set.to_list observable_mutations
                        |> List.map ~f:(fun (Local_ident.{ name; _ }, _) ->
                               name);
                    };
                span;
              };
          let s =
            {
              s with
              expr_level =
                (UA.Reducers.free_assigned_variables (function _ -> .))
                  #visit_expr () body
                |> Set.to_list
                |> List.map ~f:(fun (i, t) -> (i, dty span t));
              drop_expr = false;
            }
          in
          {
            e =
              Closure
                {
                  params = List.map ~f:dpat params;
                  body = dexpr_s s body;
                  captures =
                    List.map
                      ~f:
                        (dexpr_s
                           Instructions.zero
                           (* TODO: what to do with captures? We discard them entirely for now. Maybe we should remove that from the AST. *))
                      captures;
                };
            typ = dty span expr.typ;
            span = expr.span;
          }
      | If { cond; then_; else_ } ->
          let then_ = dexpr_same then_ in
          let else_ =
            Option.value ~default:(UA.unit_expr expr.span) else_
            |> dexpr_same |> Option.some
          in
          let cond =
            dexpr_s { s with expr_level = []; drop_expr = false } cond
          in
          { e = If { cond; then_; else_ }; typ = then_.typ; span = expr.span }
      | Match { scrutinee; arms } ->
          let arms =
            let dexpr = dexpr_same in
            let rec darm = [%inline_body darm]
            and darm' = [%inline_body darm'] in
            List.map ~f:darm arms
          in
          let typ =
            match arms with [] -> UB.never_typ | hd :: _ -> hd.arm.body.typ
          in
          let scrutinee =
            dexpr_s { s with expr_level = []; drop_expr = false } scrutinee
          in
          { e = Match { scrutinee; arms }; typ; span = expr.span }
      | Loop { body; kind; state; label; witness } ->
          let variables_to_output = s.expr_level in
          (* [adapt]: should we reorder shadowings? *)
          let observable_mutations, adapt =
            let set =
              free_assigned_variables#visit_expr () expr
              |> Set.map
                   (module UB.TypedLocalIdent)
                   ~f:(fun (i, t) -> (i, dty span t))
            in
            let idents_of_set = Set.map (module Local_ident) ~f:fst set in
            let idents_of_variables_to_output =
              variables_to_output |> List.map ~f:fst
              |> Set.of_list (module Local_ident)
            in
            (* if we mutate exactly s.expr_level, return that in this order *)
            if Set.equal idents_of_set idents_of_variables_to_output then
              (variables_to_output, false)
            else (set |> Set.to_list, true)
          in
          let s =
            {
              s with
              expr_level = observable_mutations;
              loop_level = observable_mutations;
              drop_expr = true;
            }
          in
          let empty_s = { s with expr_level = []; drop_expr = false } in
          let state : B.loop_state option =
            if List.is_empty observable_mutations then
              Option.map ~f:(dloop_state span) state
            else
              Some
                (let bpat' =
                   List.map
                     ~f:(fun (i, t) -> UB.make_var_pat i t span)
                     observable_mutations
                   |> UB.make_tuple_pat
                 in
                 let init' =
                   List.map
                     ~f:(fun (i, typ) : B.expr -> { e = LocalVar i; typ; span })
                     observable_mutations
                   |> UB.make_tuple_expr ~span
                 in
                 let witness = Features.On.state_passing_loop in
                 match state with
                 | None -> { init = init'; bpat = bpat'; witness }
                 | Some { init; bpat; _ } ->
                     {
                       init =
                         UB.make_tuple_expr ~span
                           [ init'; dexpr_s empty_s init ];
                       bpat = UB.make_tuple_pat [ bpat'; dpat bpat ];
                       witness;
                     })
          in
          let kind =
            let dexpr = dexpr_s empty_s in
            [%inline_body dloop_kind] span kind
          in
          let body = dexpr_s s body in
          (* we deal with a for loop: this is always a unit expression (i.e. no [break foo] with [foo] non-unit allowed) *)
          let typ = List.map ~f:snd observable_mutations |> UB.make_tuple_typ in
          let loop : B.expr =
            { e = Loop { body; kind; state; label; witness }; typ; span }
          in
          if adapt && not (List.is_empty variables_to_output) then
            (* here, we need to introduce the shadowings as bindings *)
            let out =
              UB.make_tuple_expr ~span
              @@ List.map
                   ~f:(fun (ident, typ) -> B.{ e = LocalVar ident; typ; span })
                   variables_to_output
            in
            let lhs =
              UB.make_tuple_pat
              @@ List.map
                   ~f:(fun (ident, typ) -> UB.make_var_pat ident typ span)
                   observable_mutations
            in
            B.
              {
                e = Let { monadic = None; lhs; rhs = loop; body = out };
                span;
                typ = out.typ;
              }
          else loop
      | [%inline_arms "dexpr'.*" - Let - Assign - Closure - Loop - If - Match]
        ->
          map (fun e ->
              let e' =
                B.{ e; typ = dty expr.span expr.typ; span = expr.span }
              in
              match e with
              | If _ | Match _ | Loop _ | Assign _ -> e'
              | _ when List.is_empty s.expr_level -> e'
              | _ ->
                  let vars =
                    List.map
                      ~f:(fun (i, typ) : B.expr ->
                        { e = LocalVar i; typ; span })
                      s.expr_level
                    |> UB.make_tuple_expr ~span
                  in
                  if s.drop_expr then
                    let effect_e' =
                      snd (SI.Hoist.collect_and_hoist_effects e')
                    in
                    if SI.SideEffects.reads_local_mut_only effect_e' then vars
                    else
                      {
                        vars with
                        e =
                          Let
                            {
                              monadic = None;
                              lhs = UB.make_wild_pat e'.typ e'.span;
                              rhs = e';
                              body = vars;
                            };
                      }
                  else UB.make_tuple_expr ~span [ vars; e' ])

    and dexpr_unwrapped e = dexpr_s Instructions.zero e
      [@@inline_ands bindings_of dexpr - dexpr']

    [%%inline_defs "Item.*"]
  end

  include Implem
end
[@@add "subtype.ml"]

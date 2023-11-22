open! Prelude

module%inlined_contents Make (F : Features.T) = struct
  open Ast
  module FA = F

  module FB = struct
    include F
    include Features.Off.Struct_pattern
  end

  include
    Phase_utils.MakeBase (F) (FB)
      (struct
        let phase_id = Diagnostics.Phase.StructPattern
      end)

  module UA = Ast_utils.Make (F)
  module UB = Ast_utils.Make (FB)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module S = struct
      include Features.SUBTYPE.Id
      include Features.Off.Struct_pattern
    end

    type 'a project_pat_accum = {
      value : 'a;
      sub_result : (B.pat * B.expr) list;
    }

    let empty_accum : unit project_pat_accum = { value = (); sub_result = [] }

    let project_pat_list (f : 'a project_pat_accum -> 'b project_pat_accum)
        (pl : 'a list project_pat_accum) : 'b list project_pat_accum =
      List.fold_left ~init:{ pl with value = [] }
        ~f:(fun y x ->
          let simple_pat = f { empty_accum with value = x } in
          {
            value = y.value @ [ simple_pat.value ];
            sub_result = y.sub_result @ simple_pat.sub_result;
          })
        pl.value

    [%%inline_defs dmutability]

    let rec dpat' (span : span) (pat : A.pat') : B.pat' =
      (project_pat' span { empty_accum with value = pat }).value

    and project_pat (p_accum : A.pat project_pat_accum) :
        B.pat project_pat_accum =
      let p = p_accum.value in
      let simple_pat = project_pat' p.span { p_accum with value = p.p } in
      {
        simple_pat with
        value = { p = simple_pat.value; span = p.span; typ = dty p.span p.typ };
      }

    and project_field_pat (p_accum : A.field_pat project_pat_accum) :
        B.field_pat project_pat_accum =
      let p = p_accum.value in
      let projections = project_pat { p_accum with value = p.pat } in
      { projections with value = { field = p.field; pat = projections.value } }

    and project_pat' (span : span) (pat_accum : A.pat' project_pat_accum) :
        B.pat' project_pat_accum =
      match pat_accum.value with
      | PWild -> { empty_accum with value = PWild }
      | PAscription { typ; typ_span; pat } ->
          let simple_pat = project_pat { pat_accum with value = pat } in
          {
            simple_pat with
            value =
              PAscription
                { typ = dty span typ; typ_span; pat = simple_pat.value };
          }
      | PConstruct { name; args; is_record = Some _; is_struct = _ } ->
          let update_args =
            project_pat_list project_field_pat { pat_accum with value = args }
          in
          let new_id =
            UB.fresh_local_ident_in_expr
              (List.map ~f:snd update_args.sub_result)
              "some_name"
          in
          {
            value =
              PBinding
                {
                  mut = Immutable;
                  mode = ByValue;
                  var = new_id (* name *);
                  typ = TApp { ident = name; args = [] };
                  (* TODO? *)
                  subpat = None;
                };
            sub_result =
              List.map
                ~f:(fun { field; pat } ->
                  ( pat,
                    ({
                       e =
                         App
                           {
                             f =
                               {
                                 e = GlobalVar field;
                                 typ = TApp { ident = field; args = [] };
                                 (* TODO *)
                                 span = pat.span;
                               };
                             args =
                               [
                                 {
                                   e = LocalVar new_id;
                                   typ = TApp { ident = name; args = [] };
                                   span = pat.span;
                                 };
                               ];
                             generic_args = [];
                             (* TODO *)
                             impl = None;
                           };
                       typ = pat.typ;
                       span = pat.span;
                     }
                      : B.expr) ))
                update_args.value
              @ update_args.sub_result;
          }
      | PConstruct { name; args; is_record = None; is_struct } ->
          let update_args =
            project_pat_list project_field_pat { pat_accum with value = args }
          in
          {
            update_args with
            value =
              PConstruct
                { name; args = update_args.value; is_record = None; is_struct };
          }
      | PArray { args } ->
          let update_args =
            project_pat_list project_pat { pat_accum with value = args }
          in
          { update_args with value = PArray { args = update_args.value } }
      | PConstant { lit } -> { empty_accum with value = PConstant { lit } }
      | PBinding { mut; mode; var : Local_ident.t; typ; subpat } ->
          let simple_pat =
            match subpat with
            | Some (subpat, as_pat) ->
                let simple_pat =
                  project_pat { pat_accum with value = subpat }
                in
                {
                  simple_pat with
                  value = Some (simple_pat.value, S.as_pattern span as_pat);
                }
            | None -> { empty_accum with value = None }
          in
          {
            simple_pat with
            value =
              PBinding
                {
                  mut = dmutability span S.mutable_variable mut;
                  mode = dbinding_mode span mode;
                  var;
                  typ = dty span typ;
                  subpat = simple_pat.value;
                };
          }
      | PDeref { subpat; witness } ->
          let simple_pat = project_pat { pat_accum with value = subpat } in
          {
            simple_pat with
            value =
              PDeref
                {
                  subpat = simple_pat.value;
                  witness = S.reference span witness;
                };
          }
      | POr { subpats } ->
          let updated_subpats =
            project_pat_list project_pat { pat_accum with value = subpats }
          in
          {
            updated_subpats with
            value = POr { subpats = updated_subpats.value };
          }

    and let_of_pat_binding ((p, rhs) : B.pat * B.expr) (body : B.expr) : B.expr
        =
      UB.make_let p rhs body

    and lets_of_pat_bindings (bindings : (B.pat * B.expr) list) (body : B.expr)
        : B.expr =
      List.fold_right ~init:body ~f:let_of_pat_binding bindings

    and dexpr' (span : span) (e : A.expr') : B.expr' =
      match (UA.unbox_underef_expr { e; span; typ = UA.never_typ }).e with
      | [%inline_arms "dexpr'.*" - Let - Closure - Loop - Match] -> auto
      | Match { scrutinee; arms } ->
          Match
            {
              scrutinee = dexpr scrutinee;
              arms =
                (project_pat_list project_darm
                   { empty_accum with value = arms })
                  .value;
            }
      | Let { monadic; lhs; rhs; body } ->
          let simple_pat = project_pat { empty_accum with value = lhs } in
          Let
            {
              monadic =
                Option.map
                  ~f:(dsupported_monads span *** S.monadic_binding span)
                  monadic;
              lhs = simple_pat.value;
              rhs = dexpr rhs;
              body = lets_of_pat_bindings simple_pat.sub_result (dexpr body);
            }
      | Loop { body; kind; state; label; witness } ->
          Loop
            {
              body = dexpr body;
              kind = dloop_kind span kind;
              state = Option.map ~f:(dloop_state span) state;
              label;
              witness = S.loop span witness;
            }
      | Closure { params; body; captures } ->
          let projected_params =
            project_pat_list project_pat { empty_accum with value = params }
          in
          Closure
            {
              params = projected_params.value;
              body =
                lets_of_pat_bindings projected_params.sub_result (dexpr body);
              captures = List.map ~f:dexpr captures;
            }

    and project_darm (arm_accum : A.arm project_pat_accum) :
        B.arm project_pat_accum =
      let arm = arm_accum.value in
      let projected_arm = project_darm' { arm_accum with value = arm.arm } in
      {
        projected_arm with
        value = { arm = projected_arm.value; span = arm.span };
      }

    and project_darm' (a_accum : A.arm' project_pat_accum) :
        B.arm' project_pat_accum =
      let a = a_accum.value in
      let simple_pat = project_pat { a_accum with value = a.arm_pat } in
      {
        simple_pat with
        value =
          {
            arm_pat = simple_pat.value;
            body = lets_of_pat_bindings simple_pat.sub_result (dexpr a.body);
          };
      }
      [@@inline_ands bindings_of dexpr]

    [%%inline_defs "Item.*"]
  end

  include Implem
end
[@@add "subtype.ml"]

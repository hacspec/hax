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
      counter : int;
      outer_expr : B.expr list;
    }

    let empty_accum : unit project_pat_accum =
      { value = (); sub_result = []; counter = 1; outer_expr = [] }

    let project_pat_list (f : 'a project_pat_accum -> 'b project_pat_accum)
        (pl : 'a list project_pat_accum) : 'b list project_pat_accum =
      List.fold_left ~init:{ pl with value = [] }
        ~f:(fun y x ->
          let simple_pat = f { y with value = x; sub_result = []; counter = y.counter + 1; } in
          {
            simple_pat with
            value = y.value @ [ simple_pat.value ];
            sub_result = y.sub_result @ simple_pat.sub_result;
          })
        pl.value

    let project_pat_option (f : 'a project_pat_accum -> 'b project_pat_accum)
        (p : 'a option project_pat_accum) : 'b option project_pat_accum =
      match p.value with
      | None -> { p with value = None }
      | Some state ->
          let dl = f { p with value = state } in
          { dl with value = Some dl.value }

    let dmutability (span : Span.t) (type a b) (s : Span.t -> a -> b)
        (mutability : a mutability) : b mutability =
      match mutability with
      | Mutable w -> Mutable (s span w)
      | Immutable -> Immutable

    let rec dpat' (span : span) (pat : A.pat') : B.pat' =
      (project_pat' span { empty_accum with value = pat }).value

    (* and dty (span : span) (ty : A.ty) : B.ty = *)
    (*   match ty with *)
    (*   | [%inline_arms "dty.*"] -> auto *)
    (* [@@inline_ands bindings_of dbinding_mode dty] *)

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
      | PWild -> { pat_accum with value = PWild }
      | PAscription { typ; typ_span; pat } ->
          let simple_pat = project_pat { pat_accum with value = pat } in
          {
            simple_pat with
            value =
              PAscription
                { typ = dty span typ; typ_span; pat = simple_pat.value };
          }
      | PConstruct { name = `TupleCons n; args; is_record = _; is_struct } ->
          (* Should be None always? *)
          let update_args =
            project_pat_list project_field_pat { pat_accum with value = args }
          in
          {
            update_args with
            value =
              PConstruct
                {
                  name = `TupleCons n;
                  args = update_args.value;
                  is_record = None;
                  is_struct;
                };
          }
      | PConstruct { name; args; is_record = Some _; is_struct = _ } ->
          let update_args =
            project_pat_list project_field_pat { pat_accum with value = args }
          in
          let outer_expr' =
            update_args.outer_expr @ List.map ~f:snd update_args.sub_result
          in
          let new_id =
            UB.fresh_local_ident_in_expr outer_expr'
              ("some_name" ^ Int.to_string update_args.counter)
          in
          let sub_result' =
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
          in
          {
            value =
              (UB.make_var_pat new_id (TApp { ident = name; args = [] }) span).p;
            sub_result = sub_result' @ update_args.sub_result;
            counter = update_args.counter + 1;
            outer_expr = outer_expr';
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

    and dbinding_mode (span : span) (binding_mode : A.binding_mode) :
        B.binding_mode =
      match binding_mode with
      | ByValue -> ByValue
      | ByRef (kind, witness) ->
          ByRef (dborrow_kind span kind, S.reference span witness)

    and dsupported_monads (span : span) (m : A.supported_monads) :
        B.supported_monads =
      match m with
      | MException t -> MException (dty span t)
      | MResult t -> MResult (dty span t)
      | MOption -> MOption

    and project_expr (e_accum : A.expr project_pat_accum) :
        B.expr project_pat_accum =
      let e = e_accum.value in
      try project_expr_unwrapped e_accum
      with Diagnostics.SpanFreeError.Exn (Data (context, kind)) ->
        let typ : B.ty =
          try dty e.span e.typ
          with Diagnostics.SpanFreeError.Exn (Data (_context, _kind)) ->
            UB.hax_failure_typ
        in
        {
          e_accum with
          value =
            UB.hax_failure_expr e.span typ (context, kind)
              (UA.LiftToFullAst.expr e);
        }

    and project_expr_unwrapped (e_accum : A.expr project_pat_accum) :
        B.expr project_pat_accum =
      let e = e_accum.value in
      let de = project_expr' e.span { e_accum with value = e.e } in
      {
        de with
        value = { e = de.value; span = e.span; typ = dty e.span e.typ };
      }

    and project_expr' (span : span) (e_accum : A.expr' project_pat_accum) :
        B.expr' project_pat_accum =
      let e = e_accum.value in
      match (UA.unbox_underef_expr { e; span; typ = UA.never_typ }).e with
      (* | [%inline_arms "dexpr'.*" - Let - Closure - Loop - Match] -> { e_accum with value = auto } *)
      | If { cond; then_; else_ } ->
          let cond' = project_expr { e_accum with value = cond } in
          let then' = project_expr { cond' with value = then_ } in
          let else' =
            project_pat_option project_expr { then' with value = else_ }
          in
          (* Option.map ~f:project_expr {e_accum with value = else_} *)
          {
            else' with
            value =
              If
                { cond = cond'.value; then_ = then'.value; else_ = else'.value };
          }
      | App { f; args; generic_args; impl } ->
          {
            e_accum with
            value =
              App
                {
                  f = dexpr f;
                  args = List.map ~f:dexpr args;
                  generic_args = List.map ~f:(dgeneric_value span) generic_args;
                  impl = Option.map ~f:(dimpl_expr span) impl;
                };
          }
      | Literal lit -> { e_accum with value = Literal lit }
      | Array l -> { e_accum with value = Array (List.map ~f:dexpr l) }
      | Construct { constructor; is_record; is_struct; fields; base } ->
          {
            e_accum with
            value =
              Construct
                {
                  constructor;
                  is_record;
                  is_struct;
                  fields = List.map ~f:(map_snd dexpr) fields;
                  base = Option.map ~f:(dexpr *** S.construct_base span) base;
                };
          }
      | Block (e, witness) ->
          { e_accum with value = Block (dexpr e, S.block span witness) }
      | LocalVar local_ident -> { e_accum with value = LocalVar local_ident }
      | GlobalVar global_ident ->
          { e_accum with value = GlobalVar global_ident }
      | Ascription { e; typ } ->
          {
            e_accum with
            value = Ascription { e = dexpr e; typ = dty span typ };
          }
      | MacroInvokation { macro; args; witness } ->
          {
            e_accum with
            value =
              MacroInvokation { macro; args; witness = S.macro span witness };
          }
      | Assign { lhs; e; witness } ->
          {
            e_accum with
            value =
              Assign
                {
                  lhs = dlhs span lhs;
                  e = dexpr e;
                  witness = S.mutable_variable span witness;
                };
          }
      | Break { e; label; witness } ->
          {
            e_accum with
            value =
              Break
                {
                  e = dexpr e;
                  label;
                  witness = (S.break span *** S.loop span) witness;
                };
          }
      | Return { e; witness } ->
          {
            e_accum with
            value = Return { e = dexpr e; witness = S.early_exit span witness };
          }
      | QuestionMark { e; converted_typ; witness } ->
          {
            e_accum with
            value =
              QuestionMark
                {
                  e = dexpr e;
                  converted_typ = dty span converted_typ;
                  witness = S.question_mark span witness;
                };
          }
      | Continue { e; label; witness = w1, w2 } ->
          {
            e_accum with
            value =
              Continue
                {
                  e = Option.map ~f:(S.state_passing_loop span *** dexpr) e;
                  label;
                  witness = (S.continue span w1, S.loop span w2);
                };
          }
      | Borrow { kind; e; witness } ->
          {
            e_accum with
            value =
              Borrow
                {
                  kind = dborrow_kind span kind;
                  e = dexpr e;
                  witness = S.reference span witness;
                };
          }
      | EffectAction { action; argument } ->
          {
            e_accum with
            value =
              EffectAction
                {
                  action = S.monadic_action span action;
                  argument = dexpr argument;
                };
          }
      | AddressOf { mut; e; witness } ->
          {
            e_accum with
            value =
              AddressOf
                {
                  mut = dmutability span S.mutable_pointer mut;
                  e = dexpr e;
                  witness = S.raw_pointer span witness;
                };
          }
      | Match { scrutinee; arms } ->
          let scrutinee' = project_expr { e_accum with value = scrutinee } in
          let arms' =
            project_pat_list project_darm { scrutinee' with value = arms; outer_expr = scrutinee'.outer_expr @ [scrutinee'.value] }
          in
          {
            arms' with
            value = Match { scrutinee = scrutinee'.value; arms = arms'.value };
          }
      | Let { monadic; lhs; rhs; body } ->
          let rhs' = project_expr { e_accum with value = rhs } in
          let lhs' =
            project_pat
              {
                rhs' with
                value = lhs;
                outer_expr = rhs'.outer_expr @ [rhs'.value];
              }
          in
          let body' = project_expr { rhs' with value = body; outer_expr = rhs'.outer_expr @ [ rhs'.value; ]; } in
          {
            lhs' with
            value =
              Let
                {
                  monadic =
                    Option.map
                      ~f:(dsupported_monads span *** S.monadic_binding span)
                      monadic;
                  lhs = lhs'.value;
                  rhs = rhs'.value;
                  body = lets_of_pat_bindings lhs'.sub_result body'.value;
                };
          }
      | Loop { body; kind; state; label; witness } ->
          let body' = project_expr { e_accum with value = body } in
          let state' =
            match state with
            | None -> { body' with value = None }
            | Some state ->
                let dl = project_loop_state span { body' with value = state } in
                { dl with value = Some dl.value }
          in
          {
            body' with
            value =
              Loop
                {
                  body = body'.value;
                  kind = dloop_kind span kind;
                  state = state'.value;
                  label;
                  witness = S.loop span witness;
                };
          }
      | Closure { params; body; captures } ->
          let body' = project_expr { e_accum with value = body } in
          let captures' =
            project_pat_list project_expr { body' with value = captures }
          in
          let projected_params =
            project_pat_list project_pat
              {
                captures' with
                value = params;
                outer_expr =
                  captures'.outer_expr @ (body'.value :: captures'.value);
              }
          in
          {
            projected_params with
            value =
              Closure
                {
                  params = projected_params.value;
                  body =
                    lets_of_pat_bindings projected_params.sub_result body'.value;
                  captures = captures'.value;
                };
          }

    (* { e with *)
    (*   value = dexpr' span e.value *)

    (* } *)

    (* and dexpr' (span : span) (e : A.expr') : B.expr' = *)

    and project_loop_kind (span : span) (k : A.loop_kind project_pat_accum) :
        B.loop_kind project_pat_accum =
      match k.value with
      | UnconditionalLoop -> { k with value = UnconditionalLoop }
      | ForLoop { it; pat; witness } ->
          let it' = project_expr { k with value = it } in
          let pat' =
            project_pat
              {
                it' with
                value = pat;
                outer_expr = it'.outer_expr @ [ it'.value ];
              }
          in
          {
            pat' with
            value =
              ForLoop
                {
                  it = it'.value;
                  pat = pat'.value;
                  witness = S.for_loop span witness;
                };
          }
      | ForIndexLoop { start; end_; var; var_typ; witness } ->
          let start' = project_expr { k with value = start } in
          let end' = project_expr { start' with value = end_ } in
          {
            end' with
            value =
              ForIndexLoop
                {
                  start = start'.value;
                  end_ = end'.value;
                  var;
                  var_typ = dty span var_typ;
                  witness = S.for_index_loop span witness;
                };
          }

    and project_loop_state (span : span)
        (s_accum : A.loop_state project_pat_accum) :
        B.loop_state project_pat_accum =
      let s = s_accum.value in
      let init' = project_expr { s_accum with value = s.init } in
      let bpat' =
        project_pat
          {
            init' with
            value = s.bpat;
            outer_expr = init'.outer_expr @ [ init'.value ];
          }
      in
      {
        bpat' with
        value =
          {
            init = init'.value;
            bpat = bpat'.value;
            witness = S.state_passing_loop span s.witness;
          };
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
      let body' = project_expr { a_accum with value = a.body } in
      let arm_pat' =
        project_pat
          {
            a_accum with
            value = a.arm_pat;
            outer_expr = a_accum.outer_expr @ [ body'.value ];
          }
      in
      {
        arm_pat' with
        value =
          {
            arm_pat = arm_pat'.value;
            body = lets_of_pat_bindings arm_pat'.sub_result body'.value;
          };
      }
      [@@inline_ands bindings_of dexpr']
    (* - dpat - dpat' - dfield_pat - dloop_kind - dloop_state - darm' *)

    [%%inline_defs "Item.*"]

    let ditem' (span : span) (item : A.item') : B.item' =
      match item with
      | Fn { name; generics; body; params } ->
          let body' = project_expr { empty_accum with value = body; } in
          B.Fn
            {
              name;
              generics = dgenerics span generics;
              body = body'.value;
              params = List.map ~f:(dparam span) params;
            }
      | Type { name; generics; variants; is_struct } ->
          B.Type
            {
              name;
              generics = dgenerics span generics;
              variants = List.map ~f:(dvariant span) variants;
              is_struct;
            }
      | TyAlias { name; generics; ty } ->
          B.TyAlias
            { name; generics = dgenerics span generics; ty = dty span ty }
      | IMacroInvokation { macro; argument; span; witness } ->
          B.IMacroInvokation
            { macro; argument; span; witness = S.macro span witness }
      | Trait { name; generics; items } ->
          B.Trait
            {
              name;
              generics = dgenerics span generics;
              items = List.map ~f:dtrait_item items;
            }
      | Impl { generics; self_ty; of_trait = trait_id, trait_generics; items }
        ->
          B.Impl
            {
              generics = dgenerics span generics;
              self_ty = dty span self_ty;
              of_trait =
                (trait_id, List.map ~f:(dgeneric_value span) trait_generics);
              items = List.map ~f:dimpl_item items;
            }
      | Alias { name; item } -> B.Alias { name; item }
      | Use { path; is_external; rename } -> B.Use { path; is_external; rename }
      | HaxError e -> B.HaxError e
      | NotImplementedYet -> B.NotImplementedYet
    (* [@@inline_ands bindings_of ditem'] *)
  end

  include Implem
end
[@@add "subtype.ml"]

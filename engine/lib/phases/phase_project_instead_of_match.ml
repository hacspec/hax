open! Prelude

module%inlined_contents Make (F : Features.T) = struct
  open Ast
  module FA = F

  module FB = struct
    include F
    include Features.Off.Project_instead_of_match
  end

  include
    Phase_utils.MakeBase (F) (FB)
      (struct
        let phase_id = Diagnostics.Phase.ProjectInsteadOfMatch
      end)

  module UA = Ast_utils.Make (F)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module S = struct
      include Features.SUBTYPE.Id
    end

    [%%inline_defs dmutability]

    (* ({ e = LocalVar ident; typ = pat.typ; span = pat.span } : A.expr) *)
    let rec project_pat (p : A.pat) : A.pat * (A.pat * A.expr) list =
      let simple_pat, remaining_pats = project_pat' p.span p.p in
      { p = simple_pat; span = p.span; typ = p.typ },
      remaining_pats
      (* List.map ~f:(fun simple_pat -> { p = simple_pat; span = p.span; typ = p.typ }) remaining_pats *)

    and project_field_pat (_span : span) (p : A.field_pat) : A.field_pat * (A.pat * A.expr) list =
      let pat, pat_list = project_pat p.pat in
      { field = p.field; pat = pat}, pat_list
      (* { field = p.field; pat = dpat p.pat } *)

    and project_pat' (span : span) (pat : A.pat') : A.pat' * (A.pat * A.expr) list =
      match pat with
      | PWild -> PWild, []
      | PAscription { typ; typ_span; pat } ->
        let simple_pat, remaining_pats = project_pat pat in
        PAscription { typ; pat = simple_pat; typ_span }, remaining_pats
      | PConstruct { name; args; is_record; is_struct } ->
        let update_args = List.map ~f:(project_field_pat span) args in
        PConstruct
          {
            name;
            args = List.map ~f:fst update_args;
            is_record;
            is_struct;
          }, List.concat_map ~f:snd update_args
      | PArray { args } ->
        let update_args = List.map ~f:project_pat args in
        PArray { args = List.map ~f:fst update_args }, List.concat_map ~f:snd update_args
      | PConstant { lit } -> PConstant { lit }, []
      | PBinding { mut; mode; var : LocalIdent.t; typ; subpat } ->
        let simple_pat, remaining_pats = match subpat with
          | Some (subpat , as_pat) ->
            let simple_pat, remaining_pats = project_pat subpat in
            Some (simple_pat, S.as_pattern as_pat), remaining_pats
          | None ->
            None, []
        in
        PBinding
          {
            mut = mut;
            mode = mode;
            var;
            typ = typ;
            subpat = simple_pat; (* TODO *) (* Option.map ~f:(dpat *** S.as_pattern) subpat; *)
          }, remaining_pats
      | PDeref { subpat; witness } ->
        let simple_pat, remaining_pats = project_pat subpat in
        PDeref { subpat = simple_pat; witness = S.reference witness }, remaining_pats

    let let_of_binding ((p, rhs) : A.pat * A.expr) (body : A.expr) : A.expr =
      UA.make_let p rhs body

    let lets_of_bindings (bindings : (A.pat * A.expr) list) (body : A.expr) :
      A.expr =
      List.fold_right ~init:body ~f:let_of_binding bindings

    let rec dexpr' (span : span) (e : A.expr') : B.expr' =
      match (UA.unbox_underef_expr { e; span; typ = UA.never_typ }).e with
      | [%inline_arms "dexpr'.*" - Let - Closure - Loop - Match] -> auto
      | Match { scrutinee; arms } ->
        Match { scrutinee = dexpr scrutinee; arms = List.map ~f:darm arms }
      | Let { monadic; lhs; rhs; body } ->
        let simple_pat, remaining_pats = project_pat lhs in
        Let
          {
            monadic =
              Option.map
                ~f:(dsupported_monads span *** S.monadic_binding)
                monadic;
            lhs = dpat simple_pat;
            rhs = dexpr rhs;
            body =
              dexpr (lets_of_bindings remaining_pats body) ;
          }
      | Loop { body; kind; state; label; witness } ->
        Loop
          {
            body = dexpr body;
            kind = dloop_kind span kind;
            state = Option.map ~f:(dloop_state span) state;
            label;
            witness = S.loop witness;
          }
      | Closure { params; body; captures } ->
        let projected_params = List.map ~f:project_pat params in
        Closure
          {
            params = List.map ~f:dpat (List.map ~f:fst projected_params);
            body = dexpr (lets_of_bindings (List.concat_map ~f:snd projected_params) body);
            captures = List.map ~f:dexpr captures;
          }

    and darm (a : A.arm) : B.arm =
      { span = a.span;
        arm =  darm' a.span a.arm}
    and darm' (_span : span) (a : A.arm') : B.arm' =
      let simple_pat, remaining_pats = project_pat a.arm_pat in
      { arm_pat = dpat simple_pat;
        body = dexpr (lets_of_bindings remaining_pats a.body) }
    [@@inline_ands bindings_of dexpr]

    [%%inline_defs "Item.*"]

    (* let rec dty (span : span) (ty : A.ty) : B.ty = *)
    (*   match ty with *)
    (*   | [%inline_arms "dty.*"] -> auto *)

    (* and dgeneric_value (span : span) (generic_value : A.generic_value) : *)
    (*   B.generic_value = *)
    (* match generic_value with *)
    (* | GLifetime { lt; witness } -> *)
    (*     GLifetime { lt; witness = S.lifetime witness } *)
    (* | GType t -> GType (dty span t) *)
    (* | GConst e -> GConst (dexpr e) *)

    (* and dpat' (span : span) (p : A.pat') : B.pat' = *)
    (*   match p with *)
    (*   | [%inline_arms "dpat'.*"] -> auto *)

  end

  include Implem
end
[@@add "subtype.ml"]

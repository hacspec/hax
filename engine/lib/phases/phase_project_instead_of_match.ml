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
  module UB = Ast_utils.Make (FB)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module S = struct
      include Features.SUBTYPE.Id
      include Features.Off.Project_instead_of_match
    end

    [%%inline_defs dmutability]

    let rec dty (span : span) (ty : A.ty) : B.ty =
      match ty with
      | [%inline_arms "dty.*"] -> auto

    and dpat' (span : span) (pat : A.pat') : B.pat' =
      match pat with
      | [%inline_arms "dpat'.*" - PConstruct] -> auto
      | PConstruct { name; args; is_record = _; is_struct } ->
        PConstruct
          {
            name;
            args = List.map ~f:(dfield_pat span) args;
            is_record = None;
            is_struct;
          }

    and project_pat (p : A.pat) : B.pat * (B.pat * B.expr) list =
      let simple_pat, remaining_pats = project_pat' p.span p.p in
      { p = simple_pat; span = p.span; typ = dty p.span p.typ },
      remaining_pats

    and project_field_pat (_span : span) (p : A.field_pat) : B.field_pat * (B.pat * B.expr) list =
      let pat, pat_list = project_pat p.pat in
      { field = p.field; pat = pat}, pat_list

    and project_pat' (span : span) (pat : A.pat') : B.pat' * (B.pat * B.expr) list =
      match pat with
      | PWild -> PWild, []
      | PAscription { typ; typ_span; pat } ->
        let simple_pat, remaining_pats = project_pat pat in
        PAscription { typ = dty span typ; pat = simple_pat; typ_span }, remaining_pats
      | PConstruct { name; args; is_record = Some _; is_struct } ->
        let update_args = List.map ~f:(project_field_pat span) args in
        let new_id = UA.fresh_local_ident_in_expr [] "some_name" in
        PConstruct
          {
            name;
            args = [{ field = name;
                      pat = {
                        p = PBinding
                            {
                              mut = Immutable;
                              mode = ByValue;
                              var = new_id (* name *);
                              typ = TApp {ident = name; args = []}; (* TODO? *)
                              subpat = None;
                            };
                        span = span ;
                        typ = TApp {ident = name; args = []}
                      }}];
            is_record = (None : FB.project_instead_of_match option);
            is_struct;
          }
      , List.map ~f:(fun ({field; pat},_) -> pat ,
                              ({ e = App {
                                   f = { e = GlobalVar field;
                                         typ = TApp { ident = field; args = [] }; (* TODO *)
                                         span = pat.span;
                                       };
                                   args = [{ e = LocalVar new_id;
                                             typ = TApp {ident = name; args = []};
                                             span = pat.span;
                                           }]};
                                  typ = pat.typ;
                                  span = pat.span } : B.expr)) update_args
        @ List.concat_map ~f:snd update_args
      | PConstruct { name; args; is_record = None; is_struct } ->
        let update_args = List.map ~f:(project_field_pat span) args in
        PConstruct
          {
            name;
            args = List.map ~f:fst update_args;
            is_record = None;
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
            mut = dmutability span S.mutable_variable mut;
            mode = dbinding_mode span mode;
            var;
            typ = dty span typ;
            subpat = simple_pat; (* TODO *) (* Option.map ~f:(dpat *** S.as_pattern) subpat; *)
          }, remaining_pats
      | PDeref { subpat; witness } ->
        let simple_pat, remaining_pats = project_pat subpat in
        PDeref { subpat = simple_pat; witness = S.reference witness }, remaining_pats

    and let_of_pat_binding ((p, rhs) : B.pat * B.expr) (body : B.expr) : B.expr =
      UB.make_let p rhs body

    and lets_of_pat_bindings (bindings : (B.pat * B.expr) list) (body : B.expr) :
      B.expr =
      List.fold_right ~init:body ~f:let_of_pat_binding bindings

    and dexpr' (span : span) (e : A.expr') : B.expr' =
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
            lhs = simple_pat;
            rhs = dexpr rhs;
            body =
               (lets_of_pat_bindings remaining_pats (dexpr body)) ;
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
            params = List.map ~f:fst projected_params;
            body = (lets_of_pat_bindings (List.concat_map ~f:snd projected_params) (dexpr body));
            captures = List.map ~f:dexpr captures;
          }

    and darm' (_span : span) (a : A.arm') : B.arm' =
      let simple_pat, remaining_pats = project_pat a.arm_pat in
      { arm_pat = simple_pat;
        body = lets_of_pat_bindings remaining_pats (dexpr a.body) }
    [@@inline_ands bindings_of dexpr]

    [%%inline_defs "Item.*"]

  end

  include Implem
end
[@@add "subtype.ml"]

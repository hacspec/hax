(** This phase rewrites patterns that don't need a guard in Rust 
    but need one in a backend. Currently it rewrites array/slice 
    patterns and usize/isize, u128/i128 patterns. *)

open! Prelude

module Make
    (F : Features.T
           with type match_guard = Features.On.match_guard
            and type slice = Features.On.slice
            and type reference = Features.On.reference) =
  Phase_utils.MakeMonomorphicPhase
    (F)
    (struct
      let phase_id = Diagnostics.Phase.RewritePatterns

      open Ast.Make (F)
      open Ast
      module U = Ast_utils.Make (F)
      module Visitors = Ast_visitors.Make (F)
      module HoistDisj = Phase_hoist_disjunctive_patterns.Make (F)

      module Error = Phase_utils.MakeError (struct
        let ctx = Diagnostics.Context.Phase phase_id
      end)

      module HoistDisjunctions = Phase_hoist_disjunctive_patterns.Make (F)

      exception IncompatibleDisjunction

      let rewrite_patterns =
        object (_self)
          inherit [_] Visitors.map as super

          method! visit_arm' () a =
            (* These booleans could allow to make this phase configurable. *)
            let rewrite_u_i_size = true in
            let rewrite_u_i_128 = true in
            let rewrite_slice_array = true in
            let pat_span = a.arm_pat.span in
            let combine_guards guards =
              match guards with
              | [] -> None
              | [ g1 ] -> Some { guard = g1; span = pat_span }
              | IfLet { witness; _ } :: _ ->
                  let lhss, rhss =
                    List.map guards ~f:(fun (IfLet { lhs; rhs; _ }) ->
                        (lhs, rhs))
                    |> List.unzip
                  in
                  Some
                    {
                      guard =
                        IfLet
                          {
                            lhs = U.make_tuple_pat lhss;
                            rhs = U.make_tuple_expr ~span:pat_span rhss;
                            witness;
                          };
                      span = pat_span;
                    }
            in

            let combine_option_guards (guards : guard option list) :
                guard option =
              List.filter_map
                ~f:(Option.map ~f:(fun (g : guard) -> g.guard))
                guards
              |> combine_guards
            in

            let rec pats_and_guards ?(forced_span : span option = None)
                ?(unfresh_exprs : expr list = []) (l : pat list) :
                pat list * guard option list =
              let pats, guards =
                List.fold_left
                  ~f:(fun (pats_left, guards_left) p ->
                    let new_p, g =
                      pat_and_guard ~forced_span p
                        ~unfresh_exprs:
                          (List.filter_map guards_left
                             ~f:
                               (Option.map ~f:(fun (g : guard) ->
                                    match g.guard with IfLet { rhs; _ } -> rhs))
                          @ unfresh_exprs)
                    in
                    (new_p :: pats_left, g :: guards_left))
                  ~init:([], []) l
              in
              (List.rev pats, List.rev guards)
            and pats_and_guard ?(forced_span : span option = None)
                ?(unfresh_exprs : expr list = []) (l : pat list) :
                pat list * guard option =
              let pats, guards =
                pats_and_guards ~forced_span ~unfresh_exprs l
              in
              let guard = combine_option_guards guards in
              (pats, guard)
            and pat_and_guard ?(unfresh_exprs : expr list = [])
                ?(forced_span : span option = None) (p : pat) :
                pat * guard option =
              let p_span = Option.value ~default:p.span forced_span in
              match p.p with
              | PArray { args; slice; suffix } ->
                  (* [pat1, pat2] should be rewritten as:
                     | array_var if let (pat1, pat2) = (array_var[0], array_var[1]) *)
                  (* In the case of slice patterns:
                     [pat1,.., pat2] should be rewritten as:
                     | array_var if let Some(pat1, pat2) =
                        if array_var.len() >= 2
                          then Some (array_var[0], array_var[array_var.len() - 1])
                          else None *)
                  (* In the case where subpatterns also have guards we need to
                        insert another pattern matching (see under). *)
                  let args_len = List.length args in
                  let suffix_len = List.length suffix in
                  let total_len = args_len + suffix_len in
                  let args_suffix, args_suffix_guards =
                    pats_and_guards ~forced_span ~unfresh_exprs (args @ suffix)
                  in
                  let args, suffix = List.split_n args_suffix args_len in
                  let combined_guard =
                    args_suffix_guards
                    |> List.filter_map
                         ~f:(Option.map ~f:(fun (g : guard) -> g.guard))
                    |> combine_guards
                  in

                  if not rewrite_slice_array then
                    ( {
                        p = PArray { args; slice; suffix };
                        span = p_span;
                        typ = p.typ;
                      },
                      combined_guard )
                  else
                    let unfresh = a.body :: unfresh_exprs in
                    let unfresh =
                      match combined_guard with
                      | Some { guard = IfLet { rhs; _ }; _ } -> rhs :: unfresh
                      | _ -> unfresh
                    in
                    let var = U.fresh_local_ident_in_expr unfresh "array_var" in
                    let array_var_expr =
                      { e = LocalVar var; span = p_span; typ = p.typ }
                    in
                    let elem_type, is_slice =
                      match p.typ with
                      | TArray { typ; _ } -> (typ, false)
                      | TSlice { ty; _ } -> (ty, true)
                      | _ ->
                          failwith
                            ("Unexpected type in array pattern: "
                            ^ [%show: ty] p.typ)
                    in
                    let usize_size = { size = SSize; signedness = Signed } in
                    let usize_typ = TInt usize_size in
                    let length =
                      let ref_var =
                        {
                          e =
                            Borrow
                              {
                                kind = Shared;
                                e = array_var_expr;
                                witness = Features.On.reference;
                              };
                          span = p_span;
                          typ =
                            TRef
                              {
                                witness = Features.On.reference;
                                region = "";
                                typ = p.typ;
                                mut = Immutable;
                              };
                        }
                      in

                      U.call Core__slice__Impl__len
                        [
                          (if is_slice then ref_var
                          else
                            U.call Rust_primitives__unsize [ ref_var ] p_span
                              (TSlice
                                 {
                                   witness = Features.On.slice;
                                   ty = ref_var.typ;
                                 }));
                        ]
                        p_span usize_typ
                    in
                    let int_literal value =
                      {
                        e =
                          Literal
                            (Int
                               {
                                 value = Int.to_string value;
                                 negative = false;
                                 kind = usize_size;
                               });
                        span = p_span;
                        typ = usize_typ;
                      }
                    in
                    let table_at i =
                      let index_expr =
                        if i < args_len then int_literal i
                        else
                          U.call Core__ops__arith__Sub__sub
                            [ length; int_literal (total_len - i) ]
                            p_span usize_typ
                      in
                      U.call Core__ops__index__Index__index
                        [ array_var_expr; index_expr ]
                        p_span elem_type
                    in
                    let args_suffix_indexed =
                      List.mapi ~f:Core.Tuple.T2.create args_suffix
                    in
                    let guard_lhs, guard_rhs_inner =
                      List.map2_exn args_suffix_indexed args_suffix_guards
                        ~f:(fun (i, p) g ->
                          match g with
                          | Some { guard = IfLet { lhs; rhs; _ }; _ } ->
                              (lhs, rhs)
                          | None -> (p, table_at i))
                      |> List.unzip
                    in
                    let length_test =
                      U.call Core__cmp__PartialOrd__ge
                        [ length; int_literal total_len ]
                        p_span usize_typ
                    in
                    let tuple_pat = U.make_tuple_pat guard_lhs in
                    let make_if_length_test then_ =
                      {
                        e =
                          If
                            {
                              cond = length_test;
                              then_;
                              else_ =
                                Some (U.make_opt_expr None p_span tuple_pat.typ);
                            };
                        span = p_span;
                        typ = then_.typ;
                      }
                    in
                    let witness = Features.On.match_guard in
                    let opt_tuple_pat =
                      U.make_opt_pattern (Some tuple_pat) p_span tuple_pat.typ
                    in
                    let tuple_rhs =
                      U.make_tuple_expr ~span:p_span guard_rhs_inner
                    in
                    let some_tuple_rhs =
                      U.make_opt_expr (Some tuple_rhs) p_span tuple_pat.typ
                    in
                    let pat_guard' : guard' =
                      match combined_guard with
                      | Some _ ->
                          (* Case with guards in the subpatterns: *)
                          (* We rewrite to the following (where pat0, ... patk)
                             correspond to the subpatterns with guards: *)
                          (* var if let Some(guard_lhs_0, pat_1, ... guard_lhs_n) =
                             if var.len() >= l then
                               match (var[0], ..., var[k]) with
                               | pat0, ... patk -> Some(guard_rhs0, var[1], ... guard_rhsn)
                               | _ -> None
                             else None*)
                          let scrutinee_list, pat_list =
                            List.map2_exn args_suffix_indexed args_suffix_guards
                              ~f:(fun (i, p) g ->
                                Option.map g ~f:(fun _ -> (table_at i, p)))
                            |> List.filter_map ~f:(Option.map ~f:(fun x -> x))
                            |> List.unzip
                          in
                          let scrutinee =
                            U.make_tuple_expr ~span:p_span scrutinee_list
                          in
                          let first_pat = U.make_tuple_pat pat_list in
                          let arms =
                            [
                              U.make_arm first_pat some_tuple_rhs p_span;
                              U.make_arm
                                (U.make_wild_pat first_pat.typ p_span)
                                (U.make_opt_expr None p_span tuple_rhs.typ)
                                p_span;
                            ]
                          in
                          let pattern_matching =
                            {
                              e = Match { scrutinee; arms };
                              span = p_span;
                              typ = opt_tuple_pat.typ;
                            }
                          in
                          let rhs = make_if_length_test pattern_matching in
                          IfLet { lhs = opt_tuple_pat; rhs; witness }
                      | None ->
                          (*
                          No guards in the subpatterns, we rewrite to:
                              | var if let Some(pat0, ... patn) =
                                if var.len() >= l then
                                  Some(var[0], ... var[n])
                                else 
                                  None
                               *)
                          (* In case this is an array pattern we can even remove
                             the length test (and we don't need the option)*)
                          let lhs =
                            if is_slice then opt_tuple_pat else tuple_pat
                          in
                          let rhs =
                            if is_slice then make_if_length_test some_tuple_rhs
                            else tuple_rhs
                          in
                          IfLet { lhs; rhs; witness }
                    in
                    ( U.make_var_pat var p.typ p_span,
                      Some { guard = pat_guard'; span = p_span } )
              | PConstruct { name; args; is_record; is_struct } ->
                  let pats, g =
                    args
                    |> List.map ~f:(fun (fp : field_pat) -> fp.pat)
                    |> pats_and_guard ~forced_span ~unfresh_exprs
                  in
                  ( {
                      p =
                        PConstruct
                          {
                            name;
                            args =
                              List.map2_exn args pats
                                ~f:(fun { field; _ } pat -> { field; pat });
                            is_record;
                            is_struct;
                          };
                      span = p_span;
                      typ = p.typ;
                    },
                    g )
              | PConstant
                  { lit = Int { value; negative; kind = { size; _ } as kind } }
                when (rewrite_u_i_size && [%eq: Ast.size] size Ast.SSize)
                     || (rewrite_u_i_128 && [%eq: Ast.size] size Ast.S128) ->
                  (* We should rewrite to: | x if let true = (x == value)*)

                  (* The variable should be free in the body of the arm,
                     and in the other already generated guards rhs
                     (this allows in particular to make sure all the
                     bindings we generate have different names). *)
                  let var =
                    U.fresh_local_ident_in_expr (a.body :: unfresh_exprs)
                      "size_var"
                  in
                  let eq_comp =
                    {
                      e =
                        App
                          {
                            f =
                              {
                                e =
                                  GlobalVar
                                    (Global_ident.of_name Value
                                       Core__cmp__PartialEq__eq);
                                span = pat_span;
                                typ = TArrow ([ TInt kind; TInt kind ], TBool);
                              };
                            args =
                              [
                                {
                                  e = Literal (Int { value; negative; kind });
                                  span = pat_span;
                                  typ = TInt kind;
                                };
                                {
                                  e = LocalVar var;
                                  span = pat_span;
                                  typ = TInt kind;
                                };
                              ];
                            generic_args = [];
                            bounds_impls = [];
                            trait = None;
                          };
                      span = pat_span;
                      typ = TBool;
                    }
                  in
                  let guard =
                    Some
                      (U.make_if_guard eq_comp pat_span Features.On.match_guard)
                  in
                  (U.make_var_pat var p.typ p_span, guard)
              | POr { subpats } -> (
                  (* The span is "forced" to make sure that equality comparison on guards lhs
                     does not fail because of spans. *)
                  let subpats, guards =
                    List.map
                      ~f:
                        (pat_and_guard ~unfresh_exprs ~forced_span:(Some p_span))
                      subpats
                    |> List.unzip
                  in
                  if guards |> combine_option_guards |> Option.is_none then
                    ({ p = POr { subpats }; span = p_span; typ = p.typ }, None)
                  else
                    (* If all guards are boolean we can take their disjunction. *)
                    let conditions =
                      List.filter_map guards
                        ~f:
                          (Option.map ~f:(fun (g : guard) ->
                               match g.guard with
                               | IfLet
                                   {
                                     rhs;
                                     lhs =
                                       { p = PConstant { lit = Bool true }; _ };
                                     _;
                                   } ->
                                   rhs
                               | _ -> raise IncompatibleDisjunction))
                    in
                    match subpats with
                    | first_pat :: other_pats
                      when List.for_all
                           (* TODO change the equality to ignore span so that we don't need forced_span *)
                             ~f:(fun p -> [%equal: pat'] p.p first_pat.p)
                             other_pats ->
                        let guard =
                          match conditions with
                          | [] -> None
                          | ({ span; _ } as e1) :: remaining_conditions ->
                              let e =
                                List.fold_left remaining_conditions ~init:e1
                                  ~f:(fun acc c ->
                                    {
                                      e =
                                        App
                                          {
                                            f =
                                              {
                                                e =
                                                  GlobalVar
                                                    (`Primitive (LogicalOp Or));
                                                span;
                                                typ =
                                                  TArrow
                                                    ([ TBool; TBool ], TBool);
                                              };
                                            args = [ acc; c ];
                                            generic_args = [];
                                            bounds_impls = [];
                                            trait = None;
                                          };
                                      span;
                                      typ = TBool;
                                    })
                              in

                              Some
                                {
                                  guard =
                                    IfLet
                                      {
                                        lhs =
                                          {
                                            p = PConstant { lit = Bool true };
                                            span;
                                            typ = TBool;
                                          };
                                        rhs = e;
                                        witness = Features.On.match_guard;
                                      };
                                  span;
                                }
                        in

                        (first_pat, guard)
                    | _ -> raise IncompatibleDisjunction)
              | PDeref { subpat; witness } ->
                  let subpat, g =
                    pat_and_guard ~forced_span ~unfresh_exprs subpat
                  in
                  ( {
                      p = PDeref { subpat; witness };
                      span = p_span;
                      typ = p.typ;
                    },
                    g )
              | PBinding { mut; mode; var; typ; subpat = Some (p, as_p) } ->
                  let subpat, g = pat_and_guard ~forced_span ~unfresh_exprs p in
                  ( {
                      p =
                        PBinding
                          { mut; mode; var; typ; subpat = Some (subpat, as_p) };
                      span = p_span;
                      typ = p.typ;
                    },
                    g )
              | PAscription { typ; typ_span; pat } ->
                  let pat, g = pat_and_guard ~forced_span ~unfresh_exprs pat in
                  ( {
                      p = PAscription { typ; typ_span; pat };
                      span = p.span;
                      typ = p.typ;
                    },
                    g )
              | PConstant _ | PWild | PBinding _ ->
                  ( { p with span = Option.value ~default:p.span forced_span },
                    None )
            in
            let arm_pat, guard = pat_and_guard a.arm_pat in
            {
              arm_pat;
              body = a.body;
              guard = combine_option_guards [ guard; a.guard ];
            }

          method! visit_expr' () e =
            (* In case a disjunction cannot be rewritten with a single guard,
               We hoist the disjunction and separate the arms. *)
            match e with
            | Match { scrutinee; arms } -> (
                try super#visit_expr' () e
                with IncompatibleDisjunction ->
                  let arms =
                    List.concat_map arms ~f:(fun arm ->
                        let arm =
                          HoistDisj.hoist_disjunctions#visit_arm () arm
                        in
                        match arm.arm.arm_pat.p with
                        | POr { subpats } ->
                            List.map subpats ~f:(fun subpat ->
                                {
                                  arm with
                                  arm = { arm.arm with arm_pat = subpat };
                                })
                        | _ -> [ arm ])
                  in
                  super#visit_expr' () (Match { arms; scrutinee }))
            | _ -> super#visit_expr' () e
        end

      let ditems = List.map ~f:(rewrite_patterns#visit_item ())
    end)

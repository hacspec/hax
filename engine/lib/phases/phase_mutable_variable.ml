open Base
open Utils

module Fix (F : Features.T) = struct
  open Ast.Make (F)

  type fix_representation = { body : expr; s_pat : pat; s_init : expr }
  [@@deriving show]

  let destruct_fix (e : expr) : fix_representation option =
    match e.e with
    | App
        {
          f =
            {
              e =
                GlobalVar
                  (`Concrete
                    { crate = "dummy"; path = Non_empty_list.("fix" :: []) });
              _;
            };
          args = [ { e = Closure { params = [ s_pat ]; body; _ }; _ }; s_init ];
        } ->
        Some { body; s_pat; s_init }
    | _ -> None
end

module%inlined_contents Make
    (F : Features.T
           with type mutable_reference = Features.Off.mutable_reference
            and type mutable_pointer = Features.Off.mutable_pointer
            and type raw_pointer = Features.Off.raw_pointer
            and type continue = Features.Off.continue
            and type arbitrary_lhs = Features.Off.arbitrary_lhs
            and type monadic_action = Features.Off.monadic_action
            and type monadic_binding = Features.Off.monadic_binding
                                                                   (* todo: this phase should require mutable borrow to be disabled *))
    (FConstraints : sig
      val early_exit : F.loop -> F.early_exit
    end) =
struct
  open Ast
  module FA = F

  module FB = struct
    include F
    include Features.Off.Mutable_variable
    include Features.Off.Loop
  end

  module B_Fix = Fix (FB)
  module UA = Ast_utils.Make (F)
  module UB = Ast_utils.Make (FB)
  module A = Ast.Make (F)
  module B = Ast.Make (FB)
  include Phase_utils.NoError
  module S = Features.SUBTYPE.Id

  let free_assigned_variables =
    UA.Reducers.free_assigned_variables (function _ -> .)

  [%%inline_defs dmutability + dty + dborrow_kind]

  let rec dpat = [%inline_body dpat]

  and dpat' (span : span) (p : A.pat') : B.pat' =
    match p with
    | [%inline_arms "dpat'.*" - PBinding - PDeref] -> auto
    | PBinding { var : LocalIdent.t; typ; subpat; _ } ->
        PBinding
          {
            mut = Immutable;
            mode = ByValue;
            var;
            typ = dty span typ;
            subpat = Option.map ~f:(dpat *** Fn.id) subpat;
          }
    | PDeref { subpat; _ } -> (dpat subpat).p

  and dfield_pat = [%inline_body dfield_pat]
  and dbinding_mode = [%inline_body dfield_pat]

  module Fresh = struct
    let state = ref 0

    let int () : int =
      let state' = !state in
      state := state' + 1;
      state'

    let local_ident (name : string) : local_ident =
      (* TODO, this gives no guarrantee of freshness whatsoever *)
      let id = int () in
      { name = name ^ Int.to_string id; id }
  end

  module MutatedVarSet = struct
    include Set.M (UB.TypedLocalIdent)

    module L = struct
      type t = UB.TypedLocalIdent.t list [@@deriving show, yojson, eq]
    end

    let show : t -> _ = Set.to_list >> [%show: L.t]
    let pp f : t -> _ = Set.to_list >> L.pp f
    let equal : t -> t -> _ = Set.equal

    let t_of_yojson : _ -> t =
      L.t_of_yojson >> Set.of_list (module UB.TypedLocalIdent)

    let yojson_of_t : t -> _ = Set.to_list >> L.yojson_of_t
  end

  module BTyLocIdentUniqueList = Ast_utils.UniqueList (UB.TypedLocalIdent)

  module ShadowingTuple = struct
    (* We consider values of type [α × β₁ × … × βₙ]
       [β₁], ... and [βₙ] are shadowed variables
    *)
    type t = {
      expr : B.expr;
      result_type : B.ty option;
      shadowings : BTyLocIdentUniqueList.t;
    }
    [@@deriving show, yojson, eq]

    let pat (val_pat : B.pat option) (t : t) : B.pat option * B.pat =
      let value =
        Option.map ~f:(fun _ -> Option.value_exn val_pat) t.result_type
      in
      let vars_of_val_pat =
        Option.map ~f:UB.Reducers.variables_of_pat value
        |> Option.value ~default:(Set.empty (module LocalIdent))
      in
      let shadowings = BTyLocIdentUniqueList.to_list t.shadowings in
      (* let value = match vars_of_val_pat with *)
      (*   | [var] when List.mem ~equal:LocalIdent.equal (List.map ~f:fst shadowings) var -> None *)
      (*   | _ -> value *)
      (* in *)
      let chunks =
        (* List.map ~f:(fun (var, ty) -> make_var_pat var ty Dummy) shadowings *)
        List.map
          ~f:(fun (var, ty) ->
            (if Set.mem vars_of_val_pat var then UB.make_wild_pat
            else UB.make_var_pat var)
              ty t.expr.span)
          shadowings
        |> List.append (Option.to_list value)
      in
      (value, UB.make_tuple_pat chunks)

    let pat' span (name : string) (t : t) : (local_ident * B.ty) option * B.pat
        =
      let val_id_ty =
        Option.map
          ~f:((fun _ -> Fresh.local_ident name) &&& Fn.id)
          t.result_type
      in
      let val_pat =
        Option.map ~f:(fun (v, t) -> UB.make_var_pat v t span) val_id_ty
      in
      let val_pat, pat = pat val_pat t in
      (Option.bind ~f:(Fn.const val_id_ty) val_pat, pat)

    let collect_mut_idents { shadowings; _ } : MutatedVarSet.t =
      Set.of_list (module UB.TypedLocalIdent)
      @@ BTyLocIdentUniqueList.to_list shadowings

    let rec pat_is_expr (p : B.pat) (e : B.expr) =
      match (p.p, e.e) with
      | B.PBinding { subpat = None; var = pv; _ }, B.LocalVar ev ->
          [%eq: local_ident] pv ev
      | ( B.PConstruct { name = pn; args = pargs; _ },
          B.Construct { constructor = en; fields = eargs; base = None; _ } )
        when [%eq: global_ident] pn en -> (
          match List.zip pargs eargs with
          | Ok zip ->
              List.for_all
                ~f:(fun (x, y) ->
                  [%eq: global_ident] x.field (fst y)
                  && pat_is_expr x.pat (snd y))
                zip
          | Unequal_lengths -> false)
      | _ -> false

    (* let make_let (lhs : B.pat) (rhs : B.expr) (body : B.expr) = *)
    (*   if pat_is_expr lhs body then rhs *)
    (*   else B.{ body with e = B.Let { lhs; rhs; body } } *)

    let with_names (val_pat : B.pat) (r : t) : B.pat option * (B.expr -> B.expr)
        =
      let val_pat, pat = pat (Some val_pat) r in
      (val_pat, UB.make_let pat r.expr)

    let with_names' (name : string) (r : t) : B.expr option * (B.expr -> B.expr)
        =
      if BTyLocIdentUniqueList.is_empty r.shadowings then
        (Option.map ~f:(Fn.const r.expr) r.result_type, Fn.id)
      else
        (* prerr_endline (name ^ " -> " ^ [%show: t] r); *)
        let val_pat, pat = pat' r.expr.span name r in
        (* (\* match val_pat wit h *\) *)
        (* (\* | Some val_pat ->  *\) *)
        (* (\* if [%eq: B.pat option] (Some pat.p) val_pat *\) *)
        let mk body =
          (* if [%eq: B.expr] body *)
          (* then r.expr *)
          (* else *)
          UB.make_let pat r.expr body
        in
        ( Option.map
            ~f:(fun (v, t) ->
              B.{ span = r.expr.span; typ = t; e = B.LocalVar v })
            val_pat,
          mk )

    let forget_all (s : t) : B.expr =
      match s.result_type with
      (* TODO: option is useless? *)
      | Some rt when UB.is_unit_typ rt -> UB.unit_expr s.expr.span
      | None -> UB.unit_expr s.expr.span
      | Some rt ->
          let e =
            match s.shadowings |> BTyLocIdentUniqueList.to_list with
            | [] -> s.expr
            | shadowings ->
                UB.map_body_of_nested_lets
                  (fun e ->
                    match e.e with
                    | B.Construct
                        {
                          constructor = `TupleCons len;
                          fields = (_, first) :: _;
                          base = None;
                          _;
                        }
                      when len = List.length shadowings + 1 ->
                        first
                    | _ -> UB.project_tuple e (List.length shadowings) 0 rt)
                  s.expr
          in
          { e with typ = rt }
  end

  module Binding = struct
    type t = {
      pat : B.pat;
      e : B.expr;
      mutated_vars : MutatedVarSet.t;
          (* mutated_vars: (local_ident * B.ty) list *)
    }
    [@@deriving show, yojson, eq]

    let collect_mut_idents { mutated_vars; _ } : MutatedVarSet.t = mutated_vars

    let with_name ({ pat = lhs; e = rhs; _ } : t) ~(body : B.expr) : B.expr =
      UB.make_let lhs rhs body

    let with_names (l : t list) ~(body : B.expr) : B.expr =
      List.fold_right l ~f:(fun b body -> with_name b ~body) ~init:body
  end

  module Result = struct
    (* Our results are of the shape
       [ let … = … in
       …
       let … = … in
       ret[, v₁, …, vₙ]
       ] *)
    type t = { bindings : Binding.t list; value : ShadowingTuple.t }
    [@@deriving show, yojson, eq]

    let collect_mut_idents_in_bindings (l : Binding.t list) : MutatedVarSet.t =
      List.fold_right
        ~f:(fun binding mut_idents ->
          let mut_idents_of_binding = Binding.collect_mut_idents binding in
          let pat_vars = UB.Reducers.variables_of_pat binding.pat in
          let scoped =
            Set.diff pat_vars
              (Set.map (module LocalIdent) ~f:fst mut_idents_of_binding)
          in
          Set.filter
            ~f:(fst >> Set.mem scoped >> not)
            (Set.union mut_idents_of_binding mut_idents))
        ~init:(Set.empty (module UB.TypedLocalIdent))
        l

    let collect_mut_idents { bindings; value } : MutatedVarSet.t =
      Set.union
        (ShadowingTuple.collect_mut_idents value)
        (collect_mut_idents_in_bindings bindings)

    let as_shadowing_tuple (r : t) (shadowings : BTyLocIdentUniqueList.t) :
        ShadowingTuple.t =
      let body =
        let shadowings = BTyLocIdentUniqueList.to_list shadowings in
        (* print_endline @@ "##################################################"; *)
        (* print_endline @@ [%show: B.expr] r.value.expr; *)
        match shadowings with
        | [] ->
            (* print_endline @@ "---> forget_all"; *)
            ShadowingTuple.forget_all r.value
        (* | [(x, _)], {e = B.LocalVar } when UB.TypedLocalIdent.(x == r.value.expr) -> r.value.expr *)
        | _ ->
            (* print_endline @@ "---> other"; *)
            let var, mk =
              ShadowingTuple.with_names' "value_as_shadow_tup" r.value
            in
            mk
            @@ UB.make_tuple_expr ~span:r.value.expr.span
            @@ Option.to_list var
            @ List.map
                ~f:(fun (v, typ) ->
                  B.{ span = r.value.expr.span; typ; e = B.LocalVar v })
                shadowings
        (* (List.map ~f:Option.some shadowings |> List.filter_map ~f:Fn.id) *)
      in
      (* [%yojson_of: BTyLocIdentUniqueList.t] shadowings |> Yojson.Safe.pretty_to_string |> prerr_endline; *)
      let expr = Binding.with_names r.bindings ~body in
      (* print_endline ("as_shadowing_tuple: " ^ [%show: B.expr] expr); *)
      { expr; shadowings; result_type = r.value.result_type }

    let from_bindings (bindings : (B.pat * t) list) (body : t) : t =
      let bindings : Binding.t list =
        List.concat_map
          ~f:(fun (pat, { bindings; value }) ->
            (* TODO: write a is_unit_expr helper *)
            if [%eq: B.expr'] value.expr.e (UB.unit_expr Dummy).e then bindings
            else
              bindings
              @ [
                  Binding.
                    {
                      pat = ShadowingTuple.pat (Some pat) value |> snd;
                      mutated_vars = ShadowingTuple.collect_mut_idents value;
                      e = value.expr;
                    };
                ])
          bindings
      in
      { bindings = bindings @ body.bindings; value = body.value }

    let seq (l : t list) (f : B.expr list -> B.expr) : t =
      if
        List.map ~f:collect_mut_idents l
        |> Set.union_list (module UB.TypedLocalIdent)
        |> Set.is_empty
      then
        let expr = f (List.map ~f:(fun { value = { expr; _ }; _ } -> expr) l) in
        {
          bindings = [];
          value =
            {
              expr;
              result_type =
                (if UB.is_unit_typ expr.typ then None else Some expr.typ);
              shadowings = BTyLocIdentUniqueList.empty;
            };
        }
      else
        let l : (Binding.t list * B.expr) list =
          List.map
            ~f:(fun { bindings; value } ->
              let has_observable_effect _e = false (* TODO *) in
              if
                Set.is_empty (ShadowingTuple.collect_mut_idents value)
                && List.is_empty bindings
                && not (has_observable_effect value.expr)
              then ([], value.expr)
              else
                let var, pat =
                  ShadowingTuple.pat' value.expr.span "arg" value
                in
                let var =
                  Option.map
                    ~f:(fun (var, typ) ->
                      B.{ e = B.LocalVar var; typ; span = pat.span })
                    var
                  |> Option.value ~default:(UB.unit_expr pat.span)
                in
                ( bindings
                  @ [
                      Binding.
                        {
                          pat;
                          e = value.expr;
                          mutated_vars = ShadowingTuple.collect_mut_idents value;
                        };
                    ],
                  var ))
            l
        in
        let bindings = List.concat_map ~f:fst l in
        let expr = f @@ List.map ~f:snd l in
        {
          bindings;
          value =
            {
              expr;
              result_type =
                (if UB.is_unit_typ expr.typ then None else Some expr.typ);
              shadowings = BTyLocIdentUniqueList.empty;
            };
        }

    include struct
      open struct
        let err () =
          failwith "Internal fatal error: Result.seq didn't kept its promise"
      end

      let seq1 (x : t) (f : B.expr -> B.expr) : t =
        seq [ x ] (function [ x ] -> f x | _ -> err ())

      let seqNp1 (x : t) (l : t list) (f : B.expr -> B.expr list -> B.expr) : t
          =
        seq (x :: l) (function x :: l -> f x l | _ -> err ())
    end

    let from_match (more : MutatedVarSet.t)
        (dexpr : MutatedVarSet.t -> A.expr -> t) (whole : A.expr)
        (scrut : A.expr) (arms : (MutatedVarSet.t * A.expr) list)
        (f : B.expr -> B.expr list -> B.expr') =
      let scrut' = dexpr more scrut in
      let vars =
        free_assigned_variables#visit_expr () whole
        |> Set.map
             (module UB.TypedLocalIdent)
             ~f:(fun (i, t) -> (i, dty Dummy t))
      in
      (* prerr_endline @@ [%show: Collect.TypedLocalIdent.t list] (Set.to_list vars); *)
      let more = Set.union more vars in
      let arms' =
        List.map
          ~f:(fun (_vars, rhs) ->
            (* what about vars? maybe put somewhere in Result.t *)
            dexpr more rhs)
          arms
      in
      let vars = BTyLocIdentUniqueList.from_set vars in
      let arms'' =
        List.map ~f:(fun arm -> (as_shadowing_tuple arm vars).expr) arms'
      in
      let r =
        seq1 scrut' (fun cond ->
            { e = f cond arms''; span = whole.span; typ = dty Dummy whole.typ })
      in
      { r with value = { r.value with shadowings = vars } }

    let pure (e0 : A.expr) (e : B.expr') : t =
      let typ = dty e0.span e0.typ in
      {
        value =
          ShadowingTuple.
            {
              expr = { e; span = e0.span; typ };
              result_type = (if UB.is_unit_typ typ then None else Some typ);
              shadowings = BTyLocIdentUniqueList.empty;
            };
        bindings = [];
      }
  end

  type loop_ctx = { continue : B.ty; break : B.ty }
  type dexpr_ctx = { vars : MutatedVarSet.t; loop : loop_ctx option }

  let rec dexpr_local (ctx : dexpr_ctx) (e : A.expr) : Result.t =
    let unsupported msg =
      failwith
        ("[desugar_mutable_variable:dexpr_local] unsupported " ^ msg
       ^ "\n\nContext:"
        ^ [%show: A.expr] e)
    in
    let e_with e' = B.{ e = e'; typ = dty e.span e.typ; span = e.span } in
    match e.e with
    | GlobalVar (`TupleCons 0)
    | Construct { constructor = `TupleCons 0; fields = []; _ } ->
        {
          bindings = [];
          value =
            {
              expr =
                {
                  span = e.span;
                  typ = dty e.span e.typ;
                  e = B.GlobalVar (`TupleCons 0);
                };
              shadowings = BTyLocIdentUniqueList.empty;
              result_type = None;
            };
        }
    | Literal lit -> Result.pure e @@ B.Literal lit
    | LocalVar v -> Result.pure e @@ B.LocalVar v
    | GlobalVar v -> Result.pure e @@ B.GlobalVar v
    | Assign
        {
          lhs =
            LhsArrayAccessor
              {
                e = LhsLocalVar { var; typ = var_typ } as lhs_local_var;
                index;
                _;
              };
          e = rhs;
          witness;
        } ->
        dexpr_local ctx
          {
            e with
            e =
              Assign
                {
                  lhs = lhs_local_var;
                  e =
                    {
                      e with
                      e =
                        App
                          {
                            f =
                              {
                                e with
                                e =
                                  A.GlobalVar
                                    (`Concrete
                                      {
                                        crate = "std";
                                        path =
                                          Non_empty_list.
                                            [
                                              "core"; "array"; "update_array_at";
                                            ];
                                      });
                                typ =
                                  A.TArrow
                                    ([ var_typ; index.typ; rhs.typ ], var_typ);
                              };
                            args =
                              [
                                { e with e = LocalVar var; typ = var_typ };
                                index;
                                rhs;
                              ];
                          };
                      typ = var_typ;
                    };
                  witness;
                };
          }
    | Assign { lhs = LhsLocalVar { var; typ = var_typ }; e = e'; _ } ->
        let e'_r = dexpr_local ctx e' in
        let var_typ = dty e.span var_typ in
        let var_pat = UB.make_var_pat var var_typ e.span in
        let _, pat = ShadowingTuple.pat (Some var_pat) e'_r.value in
        let var_binding : Binding.t =
          {
            pat;
            e = e'_r.value.expr;
            mutated_vars =
              Set.add
                (ShadowingTuple.collect_mut_idents e'_r.value)
                (var, var_typ);
          }
        in
        Result.
          {
            bindings = e'_r.bindings @ [ var_binding ];
            value =
              ShadowingTuple.
                {
                  expr = UB.unit_expr e.span;
                  result_type = None;
                  shadowings = BTyLocIdentUniqueList.empty;
                };
          }
    | Assign _ ->
        failwith "desugar_mutable_variable: TODO non-lhs-local-var assign"
    | Let _ ->
        let lets, body = UA.collect_let_bindings e in
        let lets =
          List.map ~f:(fun (p, e) -> (dpat p, dexpr_local ctx e)) lets
        in
        let r = Result.from_bindings lets (dexpr_local ctx body) in
        let value =
          Result.as_shadowing_tuple r
            (Set.union (Result.collect_mut_idents r) ctx.vars
            |> BTyLocIdentUniqueList.from_set)
        in
        { bindings = []; value }
    | App { f; args } ->
        Result.seqNp1 (dexpr_local ctx f)
          (List.map ~f:(dexpr_local ctx) args)
          (fun f args -> e_with @@ App { f; args })
    | Construct { constructor; constructs_record; fields; base } ->
        Result.seq
          (Option.to_list (Option.map ~f:(dexpr_local ctx) base)
          @ List.map ~f:(snd >> dexpr_local ctx) fields)
          (fun l ->
            let h fields_snd base =
              B.
                {
                  e =
                    B.Construct
                      {
                        constructor;
                        constructs_record;
                        fields =
                          List.zip_exn (List.map ~f:fst fields) fields_snd;
                        base;
                      };
                  typ = dty e.span e.typ;
                  span = e.span;
                }
            in
            match (l, base) with
            | base :: fields_snd, Some _ -> h fields_snd (Some base)
            | fields_snd, _ -> h fields_snd None)
    | Match { scrutinee; arms } ->
        Result.from_match ctx.vars
          (fun vars -> dexpr_local { ctx with vars })
          { e with e = Match { scrutinee = UA.unit_expr e.span; arms } }
          scrutinee
          (List.map
             ~f:(fun { arm = { body; _ }; _ } ->
               (Set.empty (module UB.TypedLocalIdent), body))
             arms)
          (fun scrutinee arms' ->
            Match
              {
                scrutinee;
                arms =
                  List.zip_exn arms arms'
                  |> List.map ~f:(fun (A.{ span; arm = { pat; _ } }, body) ->
                         B.{ span; arm = { pat = dpat pat; body } });
              })
    | If { cond; then_; else_ } ->
        Result.from_match ctx.vars
          (fun vars -> dexpr_local { ctx with vars })
          e cond
          (then_
           :: Option.to_list
                (Some (Option.value else_ ~default:(UA.unit_expr e.span)))
          |> List.map ~f:(fun e -> (Set.empty (module UB.TypedLocalIdent), e)))
          (fun cond -> function
            | [ then_; else_ ] -> If { cond; then_; else_ = Some else_ }
            | [ then_ ] -> If { cond; then_; else_ = None }
            | _ ->
                failwith
                  "Internal fatal error: Result.from_match didn't keep its \
                   promise")
    (*
    | ForLoop { start; end_; var; body; label = None; witness } ->
        (* TODO: Here, I assume there's no [break] or [continue].
           We should have two "modes" of translations. *)
        let shadowings_ = ref BTyLocIdentUniqueList.empty in
        let r =
          Result.seq
            [ dexpr_local ctx start; dexpr_local ctx end_ ]
            (function
              | [ start; end_ ] ->
                  let body_r =
                    dexpr_local
                      {
                        vars = Set.empty (module UB.TypedLocalIdent);
                        loop = None;
                      }
                      body
                  in
                  let body_r =
                    {
                      body_r with
                      value = { body_r.value with result_type = None };
                    }
                  in
                  (* failwith @@ [%show: MutatedVarSet.t] *)
                  (* @@ Result.collect_mut_idents body_r; *)
                  let body' =
                    Result.as_shadowing_tuple body_r
                    @@ BTyLocIdentUniqueList.from_set
                    @@ Result.collect_mut_idents body_r
                  in
                  shadowings_ := body'.shadowings;
                  let body = body'.expr in
                  let closure =
                    B.
                      {
                        span = body.span;
                        typ = B.TArrow ([ start.typ; body.typ ], body.typ);
                        e =
                          B.Closure
                            {
                              params =
                                [
                                  UB.make_var_pat var start.typ body.span;
                                  UB.make_tuple_pat
                                  @@ List.map ~f:(fun (v, ty) ->
                                         UB.make_var_pat v ty body.span)
                                  @@ BTyLocIdentUniqueList.to_list
                                       body'.shadowings;
                                ];
                              body;
                              captures = [];
                              (* Assumes we don't rely on captures *)
                            };
                      }
                  in
                  let fix =
                    B.
                      {
                        span = e.span;
                        typ = B.TArrow ([ closure.typ; body.typ ], body.typ);
                        e =
                          B.GlobalVar
                            (`Concrete
                              {
                                crate = "dummy";
                                path = Non_empty_list.("foldi" :: []);
                              });
                      }
                  in
                  (* failwith @@ [%show: B.ty] body.typ; *)
                  let fix_call =
                    B.
                      {
                        span = e.span;
                        typ = body.typ;
                        e =
                          B.App
                            {
                              f = fix;
                              args =
                                [
                                  start;
                                  end_;
                                  closure;
                                  UB.make_tuple_expr ~span:e.span
                                    (List.map
                                       ~f:(fun (v, typ) ->
                                         B.
                                           {
                                             span = e.span;
                                             typ;
                                             e = B.LocalVar v;
                                           })
                                       (BTyLocIdentUniqueList.to_list
                                          body'.shadowings));
                                ];
                            };
                      }
                  in
                  fix_call
              | _ ->
                  failwith
                    "Internal fatal error: Result.seq didn't keep its promise")
        in
        (* failwith @@ [%show: B.ty option] r.value.result_type; *)
        (* failwith @@ [%show: Result.t] r; *)
        {
          r with
          value = { r.value with shadowings = !shadowings_; result_type = None };
      }
      *)
    | Loop { body; label = None; _ } ->
        let vars_set =
          free_assigned_variables#visit_expr () body
          |> Set.map
               (module UB.TypedLocalIdent)
               ~f:(fun (i, t) -> (i, dty e.span t))
        in
        let vars_unique = BTyLocIdentUniqueList.from_set vars_set in
        let vars = BTyLocIdentUniqueList.to_list vars_unique in

        let break_value_typ =
          match UA.Reducers.collect_break_payloads#visit_expr () body with
          | [] -> B.TFalse
          | hd :: _ -> dty e.span hd.typ
        in
        let mk_typ t = UB.make_tuple_typ (t :: List.map ~f:snd vars) in
        let break_typ = mk_typ break_value_typ in
        let continue_typ = mk_typ break_value_typ in

        let body_r =
          dexpr_local
            {
              vars = vars_set;
              loop = Some { continue = continue_typ; break = break_typ };
            }
            body
        in
        let body' = Result.as_shadowing_tuple body_r vars_unique in
        let body_result_typ =
          Option.value ~default:UB.unit_typ body'.result_type
        in

        let body =
          UB.map_body_of_nested_lets
            (fun e -> UB.Std.Ops.ControlFlow.continue e break_typ)
            body'.expr
        in
        let closure =
          B.
            {
              span = body.span;
              typ = B.TArrow ([ body'.expr.typ ], body.typ);
              e =
                B.Closure
                  {
                    params =
                      [
                        UB.make_tuple_pat
                        @@ UB.make_wild_pat body_result_typ body.span
                           :: List.map
                                ~f:(fun (v, ty) ->
                                  UB.make_var_pat v ty body.span)
                                vars;
                      ];
                    body;
                    captures = [];
                    (* Assumes we don't rely on captures *)
                  };
            }
        in
        let fix =
          B.
            {
              span = e.span;
              typ = B.TArrow ([ closure.typ; break_typ ], break_typ);
              e =
                B.GlobalVar
                  (`Concrete
                    { crate = "dummy"; path = Non_empty_list.("fix" :: []) });
            }
        in
        let fix_call =
          B.
            {
              span = e.span;
              typ = break_typ;
              e =
                B.App
                  {
                    f = fix;
                    args =
                      [
                        closure;
                        UB.make_tuple_expr ~span:e.span
                          (UB.unit_expr e.span
                          :: List.map
                               ~f:(fun (v, typ) ->
                                 B.{ span = e.span; typ; e = B.LocalVar v })
                               (BTyLocIdentUniqueList.to_list body'.shadowings)
                          );
                      ];
                  };
            }
        in
        (match B_Fix.destruct_fix fix_call with
        | None -> failwith "None!"
        | Some _fix_call ->
            (* print_endline @@ B.show_expr @@ fix_call.body *)
            ())
        (* print_endline @@ B_Fix.show_fix_representation fix_call *);
        {
          bindings = [];
          value =
            {
              body' with
              expr = fix_call;
              result_type = Some break_value_typ;
              (* shadowings = vars_unique *)
            };
        }
    | Loop _ -> unsupported "cannot handle labels"
    | ForLoop _ -> unsupported "cannot handle labels"
    | Closure { params; body; captures } ->
        Result.pure e
        @@ B.Closure
             {
               params = List.map ~f:dpat params;
               body = dexpr body;
               captures = List.map ~f:dexpr captures;
             }
    | Break { e = payload; label; witness } ->
        dbreak_continue e ctx false payload witness
    | Continue { witness } ->
        dbreak_continue e ctx true (UA.unit_expr e.span) (snd witness)
    | Return _ when Option.is_some ctx.loop ->
        unsupported "returns inside loops"
    | Return _ -> unsupported "TODO:Return"
    | Break _ -> unsupported "TODO:Break"
    | MacroInvokation { macro; args; witness } ->
        Result.pure e @@ B.MacroInvokation { macro; args; witness }
    | Array l ->
        Result.seq
          (List.map ~f:(dexpr_local ctx) l)
          (fun l -> e_with @@ Array l)
    | Borrow { kind; e; witness } ->
        Result.seq1 (dexpr_local ctx e) (fun e' ->
            e_with
            @@ Borrow { kind = dborrow_kind e.span kind; e = e'; witness })
    | Closure _ -> unsupported "TODO:Closure"
    | Ascription { e; typ } ->
        Result.seq1 (dexpr_local ctx e) (fun e' ->
            e_with @@ Ascription { e = e'; typ = dty e.span typ })
    | AddressOf { mut; e; witness } -> .
    | MonadicAction _ -> .
  (* | _ -> failwith ("dexpr_local TODO: " ^ [%show: A.expr] e) *)

  and dexpr (e : A.expr) : B.expr =
    let e =
      dexpr_local
        { vars = Set.empty (module UB.TypedLocalIdent); loop = None }
        e
    in
    ShadowingTuple.forget_all
      (Result.as_shadowing_tuple e BTyLocIdentUniqueList.empty)

  and dbreak_continue e ctx is_continue (payload : A.expr) (witness : F.loop) =
    let r = dexpr_local ctx payload in
    let loop_types =
      Option.value_exn ~message:"Break outside of a loop?" ctx.loop
    in
    let payload =
      (Result.as_shadowing_tuple r (BTyLocIdentUniqueList.from_set ctx.vars))
        .expr
    in
    let payload =
      if is_continue then
        UB.Std.Ops.ControlFlow.continue payload loop_types.break
      else UB.Std.Ops.ControlFlow.break payload loop_types.continue
    in
    Result.
      {
        bindings = [];
        value =
          {
            expr =
              B.
                {
                  span = e.span;
                  e =
                    B.Return
                      { e = payload; witness = FConstraints.early_exit witness };
                  typ = payload.typ;
                };
            result_type = None;
            shadowings = BTyLocIdentUniqueList.empty;
          };
      }

  [%%inline_defs "Item.*"]

  let metadata = Phase_utils.Metadata.make MutableVariables
end
[@@add "subtype.ml"]

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
            };
          args = [ { e = Closure { params = [ s_pat ]; body; _ } }; s_init ];
        } ->
        Some { body; s_pat; s_init }
    | _ -> None
end

module Make
    (F : Features.T
           with type mutable_reference = Features.off
            and type mutable_pointer = Features.off
            and type raw_pointer = Features.off
            and type continue = Features.off
            and type monadic_action = Features.off
            and type monadic_binding = Features.off
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

  let rec dty (t : A.ty) : B.ty =
    match t with
    | TBool -> TBool
    | TChar -> TChar
    | TInt k -> TInt k
    | TFloat -> TFloat
    | TStr -> TStr
    | TApp { ident; args } ->
        TApp { ident; args = List.map ~f:dgeneric_value args }
    | TArray { typ; length } -> TArray { typ = dty typ; length }
    | TSlice { witness; ty } -> TSlice { witness; ty = dty ty }
    | TRef { witness; typ; mut; region } ->
        TRef { witness; typ = dty typ; mut; region }
    | TFalse -> TFalse
    | TParam local_ident -> TParam local_ident
    | TArrow (inputs, output) -> TArrow (List.map ~f:dty inputs, dty output)
    | TProjectedAssociatedType string -> TProjectedAssociatedType string
    | TRawPointer { witness } -> .

  and dgeneric_value (g : A.generic_value) : B.generic_value =
    match g with
    | GLifetime { lt; witness } -> GLifetime { lt; witness }
    | GType t -> GType (dty t)
    | GConst c -> GConst c

  let dborrow_kind (k : A.borrow_kind) : B.borrow_kind =
    match k with
    | Shared -> Shared
    | Unique -> Unique
    | Mut witness -> Mut witness

  let rec dpat (p : A.pat) : B.pat =
    { p = dpat' p.p; span = p.span; typ = dty p.typ }

  and dpat' (p : A.pat') : B.pat' =
    match p with
    | PWild -> PWild
    | PAscription { typ; typ_span; pat } ->
        PAscription { typ = dty typ; typ_span; pat = dpat pat }
    | PConstruct { name; args; record } ->
        PConstruct { name; record; args = List.map ~f:dfield_pat args }
    | PArray { args } -> PArray { args = List.map ~f:dpat args }
    | PConstant { lit } -> PConstant { lit }
    | PBinding { mut; mode; var : LocalIdent.t; typ; subpat } ->
        PBinding
          {
            mut = Immutable;
            mode = ByValue;
            var;
            typ = dty typ;
            subpat = Option.map ~f:(dpat *** Fn.id) subpat;
          }
    | PDeref { subpat } -> (dpat subpat).p
    | _ -> .

  and dfield_pat (p : A.field_pat) : B.field_pat =
    { field = p.field; pat = dpat p.pat }

  and dbinding_mode (m : A.binding_mode) : B.binding_mode =
    match m with
    | ByValue -> ByValue
    | ByRef (kind, witness) -> ByRef (dborrow_kind kind, witness)

  module Fresh = struct
    let state = ref 0

    let int () : int =
      let state' = !state in
      state := state' + 1;
      state'

    let local_ident (name : string) : local_ident =
      (* TODO, this gives no guarrantee of freshness whatsoever *)
      let id = int () in
      { name = name ^ string_of_int id; id }
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
              ty Dummy)
          shadowings
        |> List.append (Option.to_list value)
      in
      (value, UB.make_tuple_pat chunks)

    let pat' (name : string) (t : t) : (local_ident * B.ty) option * B.pat =
      let val_id_ty =
        Option.map
          ~f:((fun _ -> Fresh.local_ident name) &&& Fn.id)
          t.result_type
      in
      let val_pat =
        Option.map ~f:(fun (v, t) -> UB.make_var_pat v t Dummy) val_id_ty
      in
      let val_pat, pat = pat val_pat t in
      (Option.bind ~f:(Fn.const val_id_ty) val_pat, pat)

    let collect_mut_idents { shadowings } : MutatedVarSet.t =
      Set.of_list (module UB.TypedLocalIdent)
      @@ BTyLocIdentUniqueList.to_list shadowings

    let rec pat_is_expr (p : B.pat) (e : B.expr) =
      match (p.p, e.e) with
      | B.PBinding { subpat = None; var = pv }, B.LocalVar ev ->
          [%eq: local_ident] pv ev
      | ( B.PConstruct { name = pn; args = pargs },
          B.Construct { constructor = en; fields = eargs; base = None } )
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
        let val_pat, pat = pat' name r in
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
            ~f:(fun (v, t) -> B.{ span = Dummy; typ = t; e = B.LocalVar v })
            val_pat,
          mk )

    let forget_all (s : t) : B.expr =
      match s.result_type with
      | None -> UB.unit_expr
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

    let collect_mut_idents { mutated_vars } : MutatedVarSet.t = mutated_vars

    let with_name ({ pat = lhs; e = rhs } : t) ~(body : B.expr) : B.expr =
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
        match shadowings with
        | [] -> ShadowingTuple.forget_all r.value
        (* | [(x, _)], {e = B.LocalVar } when UB.TypedLocalIdent.(x == r.value.expr) -> r.value.expr *)
        | _ ->
            let var, mk =
              ShadowingTuple.with_names' "value_as_shadow_tup" r.value
            in
            mk
            @@ UB.make_tuple_expr ~span:r.value.expr.span
            @@ Option.to_list var
            @ List.map
                ~f:(fun (v, typ) -> B.{ span = Dummy; typ; e = B.LocalVar v })
                shadowings
        (* (List.map ~f:Option.some shadowings |> List.filter_map ~f:Fn.id) *)
      in
      (* [%yojson_of: BTyLocIdentUniqueList.t] shadowings |> Yojson.Safe.pretty_to_string |> prerr_endline; *)
      let expr = Binding.with_names r.bindings body in
      (* print_endline ("as_shadowing_tuple: " ^ [%show: B.expr] expr); *)
      { expr; shadowings; result_type = r.value.result_type }

    let from_bindings (bindings : (B.pat * t) list) (body : t) : t =
      let bindings : Binding.t list =
        List.concat_map
          ~f:(fun (pat, { bindings; value }) ->
            if [%eq: B.expr] value.expr UB.unit_expr then bindings
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
        let expr = f (List.map ~f:(fun { value = { expr } } -> expr) l) in
        {
          bindings = [];
          value =
            {
              expr;
              result_type = Some expr.typ;
              shadowings = BTyLocIdentUniqueList.empty;
            };
        }
      else
        let l : (Binding.t list * B.expr) list =
          List.map
            ~f:(fun { bindings; value } ->
              let has_observable_effect e = false (* TODO *) in
              if
                Set.is_empty (ShadowingTuple.collect_mut_idents value)
                && List.is_empty bindings
                && not (has_observable_effect value.expr)
              then ([], value.expr)
              else
                let var, pat = ShadowingTuple.pat' "arg" value in
                let var =
                  Option.map
                    ~f:(fun (var, typ) ->
                      B.{ e = B.LocalVar var; typ; span = Dummy })
                    var
                  |> Option.value ~default:UB.unit_expr
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
              result_type = Some expr.typ;
              shadowings = BTyLocIdentUniqueList.empty;
            };
        }

    let from_match (more : MutatedVarSet.t)
        (dexpr : MutatedVarSet.t -> A.expr -> t) (whole : A.expr)
        (scrut : A.expr) (arms : (MutatedVarSet.t * A.expr) list)
        (f : B.expr -> B.expr list -> B.expr') =
      let scrut' = dexpr more scrut in
      let vars =
        UA.Reducers.free_assigned_variables#visit_expr () whole
        |> Set.map (module UB.TypedLocalIdent) ~f:(fun (i, t) -> (i, dty t))
      in
      (* prerr_endline @@ [%show: Collect.TypedLocalIdent.t list] (Set.to_list vars); *)
      let more = Set.union more vars in
      let arms' =
        List.map
          ~f:(fun (vars, rhs) ->
            (* what about vars? maybe put somewhere in Result.t *)
            dexpr more rhs)
          arms
      in
      let vars = BTyLocIdentUniqueList.from_set vars in
      let arms'' =
        List.map ~f:(fun arm -> (as_shadowing_tuple arm vars).expr) arms'
      in
      let r =
        seq [ scrut' ] (function
          | [ cond ] ->
              { e = f cond arms''; span = whole.span; typ = dty whole.typ }
          | _ ->
              failwith
                "Internal fatal error: Result.seq didn't kept its promise")
      in
      { r with value = { r.value with shadowings = vars } }

    let pure (e0 : A.expr) (e : B.expr') : t =
      let typ = dty e0.typ in
      {
        value =
          ShadowingTuple.
            {
              expr = { e; span = e0.span; typ };
              result_type = Some typ;
              shadowings = BTyLocIdentUniqueList.empty;
            };
        bindings = [];
      }
  end

  type loop_ctx = { continue : B.ty; break : B.ty }
  type dexpr_ctx = { vars : MutatedVarSet.t; loop : loop_ctx option }

  let rec dexpr (ctx : dexpr_ctx) (e : A.expr) : Result.t =
    match e.e with
    | GlobalVar (`TupleCons 0)
    | Construct { constructor = `TupleCons 0; fields = [] } ->
        {
          bindings = [];
          value =
            {
              expr =
                {
                  span = e.span;
                  typ = dty e.typ;
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
          lhs = ArrayAccessor { e = { e = LocalVar var; typ = var_typ }; index };
          e = rhs;
          witness;
        } ->
        dexpr ctx
          {
            e with
            e =
              Assign
                {
                  lhs = LhsLocalVar var;
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
    | Assign { lhs = LhsLocalVar var; e = e'; witness } ->
        let e'_r = dexpr ctx e' in
        let var_typ = dty e'.typ in
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
                  expr = UB.unit_expr;
                  result_type = None;
                  shadowings = BTyLocIdentUniqueList.empty;
                };
          }
    | Let _ ->
        let lets, body = UA.collect_let_bindings e in
        let lets = List.map ~f:(fun (p, e) -> (dpat p, dexpr ctx e)) lets in
        let r = Result.from_bindings lets (dexpr ctx body) in
        let value =
          Result.as_shadowing_tuple r
            (Set.union (Result.collect_mut_idents r) ctx.vars
            |> BTyLocIdentUniqueList.from_set)
        in
        { bindings = []; value }
    | App { f; args } ->
        Result.seq
          (List.map ~f:(dexpr ctx) @@ (f :: args))
          (function
            | f :: args ->
                B.{ e = App { f; args }; typ = dty e.typ; span = e.span }
            | _ ->
                failwith
                  "Internal fatal error: Result.seq didn't keep its promise")
    | Construct { constructor; constructs_record; fields; base } ->
        Result.seq
          (Option.to_list (Option.map ~f:(dexpr ctx) base)
          @ List.map ~f:(snd >> dexpr ctx) fields)
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
                  typ = dty e.typ;
                  span = e.span;
                }
            in
            match (l, base) with
            | base :: fields_snd, Some _ -> h fields_snd (Some base)
            | fields_snd, _ -> h fields_snd None
            | _ ->
                failwith
                  "Internal fatal error: Result.seq didn't keep its promise")
    | Match { scrutinee; arms } ->
        Result.from_match ctx.vars
          (fun vars -> dexpr { ctx with vars })
          { e with e = Match { scrutinee = UA.unit_expr; arms } }
          scrutinee
          (List.map
             ~f:(fun { arm = { pat; body } } ->
               (Set.empty (module UB.TypedLocalIdent), body))
             arms)
          (fun scrutinee arms' ->
            Match
              {
                scrutinee;
                arms =
                  List.zip_exn arms arms'
                  |> List.map ~f:(fun (A.{ span; arm = { pat } }, body) ->
                         B.{ span; arm = { pat = dpat pat; body } });
              })
    | If { cond; then_; else_ } ->
        (* TODO: None [else_] + mutation in [then_] *)
        Result.from_match ctx.vars
          (fun vars -> dexpr { ctx with vars })
          e cond
          (then_ :: Option.to_list else_
          |> List.map ~f:(fun e -> (Set.empty (module UB.TypedLocalIdent), e)))
          (fun cond -> function
            | [ then_; else_ ] -> If { cond; then_; else_ = Some else_ }
            | [ then_ ] -> If { cond; then_; else_ = None }
            | _ ->
                failwith
                  "Internal fatal error: Result.from_match didn't keep its \
                   promise")
    | ForLoop { start; end_; var; body; label = None; witness } ->
        (* TODO: Here, I assume there's no [break] or [continue].
           We should have two "modes" of translations. *)
        Result.seq
          [ dexpr ctx start; dexpr ctx end_ ]
          (function
            | [ start; end_ ] ->
                let body_r =
                  dexpr
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
                let body' =
                  Result.as_shadowing_tuple body_r
                  @@ BTyLocIdentUniqueList.from_set
                  @@ Result.collect_mut_idents body_r
                in
                let body = body'.expr in
                let closure =
                  B.
                    {
                      span = body.span;
                      typ = B.TArrow ([ start.typ; body'.expr.typ ], body.typ);
                      e =
                        B.Closure
                          {
                            params =
                              [
                                UB.make_var_pat var start.typ Dummy;
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
                      typ = B.TArrow ([ closure.typ; UB.unit_typ ], UB.unit_typ);
                      e =
                        B.GlobalVar
                          (`Concrete
                            {
                              crate = "dummy";
                              path = Non_empty_list.("foldi" :: []);
                            });
                    }
                in
                let fix_call =
                  B.
                    {
                      span = e.span;
                      typ = UB.unit_typ;
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
    | Loop { body; label = None; witness } ->
        let vars_set =
          UA.Reducers.free_assigned_variables#visit_expr () body
          |> Set.map (module UB.TypedLocalIdent) ~f:(fun (i, t) -> (i, dty t))
        in
        let vars_unique = BTyLocIdentUniqueList.from_set vars_set in
        let vars = BTyLocIdentUniqueList.to_list vars_unique in

        let break_value_typ =
          match UA.Reducers.collect_break_payloads#visit_expr () body with
          | [] -> B.TFalse
          | hd :: _ -> dty hd.typ
        in
        let mk_typ t = UB.make_tuple_typ (t :: List.map ~f:snd vars) in
        let break_typ = mk_typ break_value_typ in
        let continue_typ = mk_typ break_value_typ in

        let body_r =
          dexpr
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
                          (UB.unit_expr
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
        | Some fix_call ->
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
    | Closure { params; body; captures } ->
        Result.pure e
        @@ B.Closure
             {
               params = List.map ~f:dpat params;
               body = dexpr_top body;
               captures = List.map ~f:dexpr_top captures;
             }
    | Break { e = payload; label; witness } ->
        dbreak_continue e ctx false payload witness
    | Continue { witness } ->
        dbreak_continue e ctx true UA.unit_expr (snd witness)
    | Return _ when Option.is_some ctx.loop ->
        failwith "Returns inside loops are not supported"
    | _ -> failwith ("dexpr TODO: " ^ [%show: A.expr] e)

  and dexpr_top (e : A.expr) : B.expr =
    let e =
      dexpr { vars = Set.empty (module UB.TypedLocalIdent); loop = None } e
    in
    ShadowingTuple.forget_all
      (Result.as_shadowing_tuple e BTyLocIdentUniqueList.empty)

  and dbreak_continue e ctx is_continue (payload : A.expr) (witness : F.loop) =
    let r = dexpr ctx payload in
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

  let dtrait_ref (r : A.trait_ref) : B.trait_ref =
    {
      trait = r.trait;
      args = List.map ~f:dgeneric_value r.args;
      bindings = r.bindings;
    }

  let dgeneric_param (p : A.generic_param) : B.generic_param =
    match p with
    | GPLifetime { ident; witness } -> GPLifetime { ident; witness }
    | GPType { ident; default } ->
        GPType { ident; default = Option.map ~f:dty default }
    | GPConst { ident; typ } -> GPConst { ident; typ = dty typ }

  let dgeneric_constraint (p : A.generic_constraint) : B.generic_constraint =
    match p with
    | GCLifetime (lf, witness) -> B.GCLifetime (lf, witness)
    | GCType { typ; implements } ->
        B.GCType { typ = dty typ; implements = dtrait_ref implements }

  let dgenerics (g : A.generics) : B.generics =
    {
      params = List.map ~f:dgeneric_param g.params;
      constraints = List.map ~f:dgeneric_constraint g.constraints;
    }

  let dparam (p : A.param) : B.param =
    { pat = dpat p.pat; typ = dty p.typ; typ_span = p.typ_span }

  let dvariant (v : A.variant) : B.variant =
    { name = v.name; arguments = List.map ~f:(map_snd dty) v.arguments }

  let ditem (item : A.item) : B.item =
    let v =
      match item.v with
      | Fn { name; generics; body; params } ->
          B.Fn
            {
              name;
              generics = dgenerics generics;
              body = dexpr_top body;
              params = List.map ~f:dparam params;
            }
      | Type { name; generics; variants; record } ->
          B.Type
            {
              name;
              generics = dgenerics generics;
              variants = List.map ~f:dvariant variants;
              record;
            }
      | TyAlias { name; generics; ty } ->
          B.TyAlias { name; generics = dgenerics generics; ty = dty ty }
      | NotImplementedYet -> B.NotImplementedYet
    in
    { v; span = item.span; parent_namespace = item.parent_namespace }

  let metadata = Desugar_utils.Metadata.make "MutableVariables"
end

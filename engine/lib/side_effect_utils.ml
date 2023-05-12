open Base
open Utils

module MakeSI
    (F : Features.T with type monadic_binding = Features.Off.monadic_binding) =
struct
  module AST = Ast.Make (F)
  module U = Ast_utils.Make (F)
  include Ast
  include AST

  module SideEffects = struct
    (* TODO: consider non-terminaison and closed-mutation *)
    type t = {
      reads_local_mut : U.Sets.TypedLocalIdent.t;  (** only free variables *)
      writes_local_mut : U.Sets.TypedLocalIdent.t;  (** only free variables *)
      deep_mutation : bool;
      return : ty option;
      continue : ty option option; (* TODO: continue with labels *)
      break : ty option; (* TODO: break with labels *)
    }

    let zero : t =
      {
        reads_local_mut = Set.empty (module U.TypedLocalIdent);
        writes_local_mut = Set.empty (module U.TypedLocalIdent);
        deep_mutation = false;
        return = None;
        continue = None;
        break = None;
      }

    let plus : t -> t -> t =
      let merge_ty x y =
        assert ([%eq: ty] x y);
        x
      in
      fun x y ->
        {
          reads_local_mut = Set.union x.reads_local_mut y.reads_local_mut;
          writes_local_mut = Set.union x.writes_local_mut y.writes_local_mut;
          deep_mutation = x.deep_mutation || y.deep_mutation;
          return = Option.map2 ~f:merge_ty x.return y.return;
          continue =
            Option.map2
              ~f:(fun x y ->
                match (x, y) with
                | Some x, Some y -> Some (merge_ty x y)
                | _ -> None)
              x.continue y.continue;
          break = Option.map2 ~f:merge_ty x.break y.break;
        }

    let reads (var : LocalIdent.t) (ty : ty) =
      {
        zero with
        reads_local_mut = Set.singleton (module U.TypedLocalIdent) (var, ty);
      }

    let writes (var : LocalIdent.t) (ty : ty) =
      {
        zero with
        writes_local_mut = Set.singleton (module U.TypedLocalIdent) (var, ty);
      }

    let no_deep_mut_or_cf : t -> bool =
      [%matches?
        {
          deep_mutation = false;
          return = None;
          continue = None;
          break = None;
          _;
        }]

    let reads_local_mut_only : t -> bool =
     fun x -> no_deep_mut_or_cf x && Set.is_empty x.writes_local_mut

    let commute : t -> t -> bool =
      curry @@ function
      (* | x, y when pure x && pure y -> true *)
      | ( ({ reads_local_mut = xr; writes_local_mut = xw; _ } as x),
          ({ reads_local_mut = yr; writes_local_mut = yw; _ } as y) )
        when no_deep_mut_or_cf x && no_deep_mut_or_cf y ->
          let open Set in
          let x = union xw xr in
          let y = union yw yr in
          is_empty @@ union (inter xw y) (inter yw x)
      | _ -> false

    class ['s] monoid =
      object
        inherit ['s] VisitorsRuntime.monoid
        method private zero = zero
        method private plus = plus
      end

    let without_rw_vars (vars : U.Sets.LocalIdent.t) (effects : t) =
      let without = Set.filter ~f:(fst >> Set.mem vars >> not) in
      {
        effects with
        writes_local_mut = without effects.writes_local_mut;
        reads_local_mut = without effects.reads_local_mut;
      }
  end

  module Hoist = struct
    type binding = pat * expr
    type t = binding list * SideEffects.t

    let plus : t -> t -> t =
     fun (lbs1, e1) (lbs2, e2) -> (lbs1 @ lbs2, SideEffects.plus e1 e2)

    let zero : t = ([], SideEffects.zero)

    class ['s] monoid =
      object
        inherit ['s] VisitorsRuntime.monoid
        method private zero = zero
        method private plus = plus
      end

    class ['s] bool_monoid =
      object
        inherit ['s] VisitorsRuntime.monoid
        method private zero = false
        method private plus = ( && )
      end

    module CollectContext = struct
      type t = { mutable fresh_id : int }

      let fresh_local_ident (self : t) : LocalIdent.t =
        self.fresh_id <- self.fresh_id + 1;
        { name = "hoist" ^ Int.to_string self.fresh_id; id = -1 }

      let empty = { fresh_id = 0 }
    end

    module HoistSeq = struct
      let ( let* ) x f = Option.bind ~f x

      let many (ctx : CollectContext.t) (l : (expr * t) list)
          (next : expr list -> t -> expr * t) =
        assert (not @@ List.is_empty l);
        let fresh () = CollectContext.fresh_local_ident ctx in
        let effects, l =
          List.fold_right l ~init:(SideEffects.zero, [])
            ~f:(fun (e, (lbs, effect)) (effects, l) ->
              ( SideEffects.plus effect effects,
                (if
                 SideEffects.reads_local_mut_only effect
                 && SideEffects.commute effect effects
                then (lbs, e)
                else
                  let var = fresh () in
                  ( lbs @ [ (U.make_var_pat var e.typ e.span, e) ],
                    { e with e = LocalVar var } ))
                :: l ))
        in
        let lbs = List.concat_map ~f:fst l in
        next (List.map ~f:snd l) (lbs, effects)

      let err_hoist_invariant (type r) (location : string) : r =
        Diagnostics.failure ~context:(Other "HoistSeq") ~span:Dummy
          (AssertionFailure
             {
               details =
                 "[HoistSeq.many] broke its invariant (location:" ^ location
                 ^ ")";
             })

      let one (ctx : CollectContext.t) (e : expr * t)
          (next : expr -> t -> expr * t) =
        many ctx [ e ] (function
          | [ e ] -> next e
          | _ -> err_hoist_invariant Caml.__LOC__)
    end

    let let_of_binding ((pat, rhs) : pat * expr) (body : expr) : expr =
      U.make_let pat rhs body

    let lets_of_bindings (bindings : (pat * expr) list) (body : expr) : expr =
      List.fold_right ~init:body ~f:let_of_binding bindings

    let collect_and_hoist_effects_object =
      object
        inherit [_] expr_mapreduce as super
        inherit [_] monoid as m
        method visit_t _ x = (x, m#zero)
        method visit_mutability _ _ x = (x, m#zero)

        (* Collecting effects bottom up *)
        method visit_LhsLocalVar _ var typ =
          (LhsLocalVar { var; typ }, ([], SideEffects.writes var typ))

        method visit_LhsArbitraryExpr _ e witness =
          let deep_mutation =
            (object
               inherit [_] expr_reduce
               inherit [_] bool_monoid as m
               method visit_t _ _ = m#zero
               method visit_mutability _ _ _ = m#zero
               method visit_Deref _ _ _ = true
            end)
              #visit_expr
              () e
          in
          ( LhsArbitraryExpr { e; witness },
            ([], { SideEffects.zero with deep_mutation }) )

        method visit_expr (env : CollectContext.t) e =
          match e.e with
          | LocalVar v -> (e, ([], SideEffects.reads v e.typ))
          | Return { e = e'; witness } ->
              HoistSeq.one env (super#visit_expr env e') (fun e' effects ->
                  ( { e with e = Return { e = e'; witness } },
                    m#plus effects
                      ([], { SideEffects.zero with return = Some e'.typ }) ))
          | Break { e = e'; label; witness } ->
              HoistSeq.one env (super#visit_expr env e') (fun e' effects ->
                  ( { e with e = Break { e = e'; label; witness } },
                    m#plus effects
                      ([], { SideEffects.zero with break = Some e'.typ }) ))
          | Continue { e = e'; label; witness } -> (
              let ceffect =
                ( [],
                  {
                    SideEffects.zero with
                    continue = Some (Option.map ~f:(fun (_, e) -> e.typ) e');
                  } )
              in
              match e' with
              | Some (witness', e') ->
                  HoistSeq.one env (super#visit_expr env e') (fun e' effects ->
                      ( {
                          e with
                          e =
                            Continue { e = Some (witness', e'); label; witness };
                        },
                        m#plus ceffect effects ))
              | None -> (e, ceffect))
          | Loop { body; kind; state; label; witness } ->
              let kind' =
                match kind with
                | UnconditionalLoop -> []
                | ForLoop { start; end_; _ } ->
                    [ super#visit_expr env start; super#visit_expr env end_ ]
              in
              let state' =
                Option.map
                  ~f:(fun { init; _ } -> super#visit_expr env init)
                  state
              in
              let kind_state = kind' @ Option.to_list state' in
              (* effects to realize before the loop *)
              (* let effects_before = List.fold ~init:zero ~f:plus kind_state in *)
              HoistSeq.many env kind_state (fun l effects ->
                  let kind =
                    match (l, kind) with
                    | ( start :: end_ :: ([ _ ] | []),
                        ForLoop { var; witness; var_typ; _ } ) ->
                        ForLoop { var; witness; start; end_; var_typ }
                    | ([ _ ] | []), UnconditionalLoop -> UnconditionalLoop
                    | _ -> HoistSeq.err_hoist_invariant Caml.__LOC__
                  in
                  let state =
                    match (l, state) with
                    | ( (_ :: _ :: [ state ] | [ state ]),
                        Some { witness; bpat; _ } ) ->
                        Some { witness; bpat; init = state }
                    | ([ _; _ ] | []), None -> None
                    | _ -> HoistSeq.err_hoist_invariant Caml.__LOC__
                  in
                  (* by now, the "inputs" of the loop are hoisted as let if needed *)
                  let body, (lbs, body_effects) = super#visit_expr env body in
                  (* the loop construction **handles** the effect continue and break *)
                  let body_effects =
                    ([], { body_effects with continue = None; break = None })
                  in
                  let effects = m#plus effects body_effects in
                  let body = lets_of_bindings lbs body in
                  ( { e with e = Loop { body; kind; state; label; witness } },
                    effects ))
          | If { cond; then_; else_ } ->
              HoistSeq.one env (super#visit_expr env cond) (fun cond effects ->
                  let then_, (lbs_then, ethen) = super#visit_expr env then_ in
                  let else_, (lbs_else, eelse) =
                    match Option.map ~f:(super#visit_expr env) else_ with
                    | Some (else_, eelse) -> (Some else_, eelse)
                    | None -> (None, m#zero)
                  in
                  let then_ = lets_of_bindings lbs_then then_ in
                  let else_ = Option.map ~f:(lets_of_bindings lbs_else) else_ in
                  let effects =
                    m#plus (m#plus ([], ethen) ([], eelse)) effects
                  in
                  ({ e with e = If { cond; then_; else_ } }, effects))
          | App { f; args } ->
              HoistSeq.many env
                (List.map ~f:(super#visit_expr env) (f :: args))
                (fun l effects ->
                  let f, args =
                    match l with
                    | f :: args -> (f, args)
                    | _ -> HoistSeq.err_hoist_invariant Caml.__LOC__
                  in
                  ({ e with e = App { f; args } }, effects))
          | Literal _ -> (e, m#zero)
          | Array l ->
              HoistSeq.many env
                (List.map ~f:(super#visit_expr env) l)
                (fun l effects -> ({ e with e = Array l }, effects))
          | Construct { constructor; constructs_record; fields; base } ->
              HoistSeq.many env
                (List.map ~f:(super#visit_expr env)
                   (Option.to_list base @ List.map ~f:snd fields))
                (fun l effects ->
                  let base, fields_expr =
                    match (l, base) with
                    | hd :: tl, Some _ -> (Some hd, tl)
                    | _, None -> (None, l)
                    | _ -> HoistSeq.err_hoist_invariant Caml.__LOC__
                  in
                  let fields =
                    match List.zip (List.map ~f:fst fields) fields_expr with
                    | Ok fields -> fields
                    | Unequal_lengths ->
                        HoistSeq.err_hoist_invariant Caml.__LOC__
                  in
                  ( {
                      e with
                      e =
                        Construct
                          { constructor; constructs_record; fields; base };
                    },
                    effects ))
          | Match { scrutinee; arms } ->
              let arms, eff_arms =
                let arms =
                  List.map ~f:(super#visit_arm env) arms
                  (* materialize letbindings in each arms *)
                  |> List.map ~f:(fun ({ arm; span }, ((lbs, effects) : t)) ->
                         let arm =
                           { arm with body = lets_of_bindings lbs arm.body }
                         in
                         (({ arm; span } : arm), ([], effects)))
                     (* cancel effects that concern variables introduced in pats  *)
                  |> List.map ~f:(fun (arm, (lbs, effects)) ->
                         let vars = U.Reducers.variables_of_pat arm.arm.pat in
                         (arm, (lbs, SideEffects.without_rw_vars vars effects)))
                in
                ( List.map ~f:fst arms,
                  List.fold ~init:m#zero ~f:m#plus (List.map ~f:snd arms) )
              in
              HoistSeq.one env (super#visit_expr env scrutinee)
                (fun scrutinee effects ->
                  ( { e with e = Match { scrutinee; arms } },
                    m#plus eff_arms effects ))
          | Let { monadic = Some _; _ } -> .
          | Let { monadic = None; lhs; rhs; body } ->
              let rhs, (rhs_lbs, rhs_effects) = super#visit_expr env rhs in
              let body, (body_lbs, body_effects) = super#visit_expr env body in
              let lbs = rhs_lbs @ ((lhs, rhs) :: body_lbs) in
              let effects = SideEffects.plus rhs_effects body_effects in
              (body, (lbs, effects))
          | GlobalVar _ -> (e, m#zero)
          | Ascription { e = e'; typ } ->
              HoistSeq.one env (super#visit_expr env e') (fun e' eff ->
                  ({ e with e = Ascription { e = e'; typ } }, eff))
          | MacroInvokation _ -> (e, m#zero)
          | Assign { lhs; e = e'; witness } ->
              (* TODO: here, LHS should really have no effect... This is not fine *)
              let lhs, lhs_effects = super#visit_lhs env lhs in
              HoistSeq.one env (super#visit_expr env e') (fun e' effects ->
                  let effects = m#plus effects lhs_effects in
                  ({ e with e = Assign { e = e'; lhs; witness } }, effects))
          | Borrow { kind; e = e'; witness } ->
              let kind, kind_effects = super#visit_borrow_kind env kind in
              HoistSeq.one env (super#visit_expr env e') (fun e' effects ->
                  let effects = m#plus kind_effects effects in
                  ({ e with e = Borrow { kind; e = e'; witness } }, effects))
          | AddressOf { mut; e = e'; witness } ->
              (* let mut, mut_effects = super#visit_mutability env kind in *)
              let mut, mut_effects = (mut, m#zero) in
              HoistSeq.one env (super#visit_expr env e') (fun e' effects ->
                  let effects = m#plus mut_effects effects in
                  ({ e with e = AddressOf { mut; e = e'; witness } }, effects))
          | Closure { params; body; captures } ->
              let body, body_effects =
                let body, (lbs, effects) = super#visit_expr env body in
                let vars =
                  Set.union_list (module LocalIdent)
                  @@ List.map ~f:U.Reducers.variables_of_pat params
                in
                let body = lets_of_bindings lbs body in
                (body, ([], SideEffects.without_rw_vars vars effects))
              in
              ({ e with e = Closure { params; body; captures } }, body_effects)
              (* HoistSeq.many env *)
              (*   (List.map ~f:(super#visit_expr env) captures) *)
              (*   (fun captures effects -> *)
              (*     let effects = m#plus body_effects effects in *)
              (*     ({ e with e = Closure { params; body; captures } }, effects)) *)
          | EffectAction _ ->
              Diagnostics.failure
                ~context:(Other "collect_and_hoist_effects_object") ~span:e.span
                (Unimplemented
                   { issue_id = None; details = Some "EffectAction" })
      end

    let collect_and_hoist_effects (e : expr) : expr * SideEffects.t =
      let e, (lbs, effects) =
        collect_and_hoist_effects_object#visit_expr CollectContext.empty e
      in
      (lets_of_bindings lbs e, effects)
  end
end

module%inlined_contents Hoist
    (F : Features.T with type monadic_binding = Features.Off.monadic_binding) =
struct
  module FA = F

  module FB = struct
    include F
  end

  module UA = Ast_utils.Make (F)
  module UB = Ast_utils.Make (FB)
  module A = Ast.Make (F)
  module B = Ast.Make (FB)
  include Phase_utils.NoError
  module S = Features.SUBTYPE.Id
  open MakeSI (F)

  [%%inline_defs dmutability + dty + dborrow_kind + dpat]

  module ID = struct
    (* OCaml is not able to understand A.expr is the same as B.expr........... *)
    [%%inline_defs dexpr]
  end

  let dexpr (expr : A.expr) : B.expr =
    Hoist.collect_and_hoist_effects expr |> fst |> ID.dexpr

  [%%inline_defs "Item.*"]

  let metadata = Phase_utils.Metadata.make HoistSideEffects
end
[@@add "subtype.ml"]

module%inlined_contents MutVar
    (F : Features.T
           with type mutable_reference = Features.Off.mutable_reference
            and type mutable_pointer = Features.Off.mutable_pointer
            and type raw_pointer = Features.Off.raw_pointer
            and type arbitrary_lhs = Features.Off.arbitrary_lhs
            and type nontrivial_lhs = Features.Off.nontrivial_lhs
            and type monadic_action = Features.Off.monadic_action
            and type monadic_binding = Features.Off.monadic_binding
    (* todo: this phase should require mutable borrow to be disabled *)) =
(* (FConstraints : sig *)
(*   val early_exit : F.loop -> F.early_exit *)
(* end) *)
struct
  open Ast
  module FA = F

  let metadata = Phase_utils.Metadata.make LocalMutation

  module FB = struct
    include F
    include Features.Off.Mutable_variable
    include Features.On.State_passing_loop
  end

  module UA = Ast_utils.Make (F)
  module UB = Ast_utils.Make (FB)
  module A = Ast.Make (F)
  module B = Ast.Make (FB)
  include Phase_utils.DefaultError

  module S = struct
    include Features.SUBTYPE.Id

    let state_passing_loop _ = Features.On.state_passing_loop
  end

  [%%inline_defs dmutability + dty + dborrow_kind]

  let rec dpat : A.pat -> B.pat = [%inline_body dpat]

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

  let free_assigned_variables =
    UA.Reducers.free_assigned_variables (function _ -> .)

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

  (* [s] is the list of variables the last expression should return, packed in a tuple *)
  let rec dexpr_s (s : Instructions.t) (expr : A.expr) : B.expr =
    let rec dexpr e = dexpr_s s e
    and dloop_state = [%inline_body dloop_state]
    and darm = [%inline_body darm]
    and darm' = [%inline_body darm'] (* and dlhs = [%inline_body dlhs] *) in
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
                body = dexpr body;
              };
          typ = dty span expr.typ;
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
        {
          e =
            Let
              {
                monadic = None;
                lhs = lhs';
                rhs = dexpr_s { s with expr_level = rhs_vars; drop_expr } rhs;
                body = dexpr body;
              };
          typ = dty span expr.typ;
          span = expr.span;
        }
    | Assign { e; lhs = LhsLocalVar { var; _ }; _ } ->
        let vars =
          List.map
            ~f:(fun (i, typ) : B.expr ->
              if LocalIdent.equal i var then
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
        let observable_mutations = free_assigned_variables#visit_expr () expr in
        if observable_mutations |> Set.is_empty |> not then
          raise
          @@ Error.E
               {
                 kind =
                   ClosureMutatesParentBindings
                     {
                       bindings =
                         Set.to_list observable_mutations
                         |> List.map ~f:(fun (LocalIdent.{ name; _ }, _) ->
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
        {
          e =
            If
              {
                cond =
                  dexpr_s { s with expr_level = []; drop_expr = false } cond;
                then_ = dexpr then_;
                else_ = Option.map ~f:dexpr else_;
              };
          typ = dty span expr.typ;
          span = expr.span;
        }
    | Match { scrutinee; arms } ->
        {
          e =
            Match
              {
                scrutinee =
                  dexpr_s
                    { s with expr_level = []; drop_expr = false }
                    scrutinee;
                arms = List.map ~f:darm arms;
              };
          typ = dty span expr.typ;
          span = expr.span;
        }
    | Loop { body; kind; state; label; witness } ->
        let variables_to_output = s.expr_level in
        let observable_mutations, adapt =
          let set =
            free_assigned_variables#visit_expr () expr
            |> Set.map
                 (module UB.TypedLocalIdent)
                 ~f:(fun (i, t) -> (i, dty span t))
          in
          (* if we mutate exactly s.expr_level, return that in this order *)
          if
            Set.equal
              (Set.map (module LocalIdent) ~f:fst set)
              (variables_to_output |> List.map ~f:fst
              |> Set.of_list (module LocalIdent))
          then (variables_to_output, true)
          else (set |> Set.to_list, false)
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
                       UB.make_tuple_expr ~span [ init'; dexpr_s empty_s init ];
                     bpat = UB.make_tuple_pat [ bpat'; dpat bpat ];
                     witness;
                   })
        in
        let kind =
          let dexpr = dexpr_s empty_s in
          [%inline_body dloop_kind] span kind
        in
        let body = dexpr_s s body in
        let expr_typ = dty span expr.typ in
        let loop : B.expr =
          {
            e = Loop { body; kind; state; label; witness };
            typ =
              (if List.is_empty observable_mutations then
               UB.make_tuple_typ
                 [
                   List.map ~f:snd observable_mutations |> UB.make_tuple_typ;
                   expr_typ;
                 ]
              else expr_typ);
            span;
          }
        in
        if adapt && not (List.is_empty variables_to_output) then loop else loop
    | [%inline_arms "dexpr'.*" - Let - Assign - Closure - Loop - If - Match] ->
        map (fun e ->
            let e' = B.{ e; typ = dty expr.span expr.typ; span = expr.span } in
            match e with
            | If _ | Match _ | Loop _ | Assign _ -> e'
            | _ when List.is_empty s.expr_level -> e'
            | _ ->
                let vars =
                  List.map
                    ~f:(fun (i, typ) : B.expr -> { e = LocalVar i; typ; span })
                    s.expr_level
                  |> UB.make_tuple_expr ~span
                in
                if s.drop_expr then vars
                else UB.make_tuple_expr ~span [ vars; e' ])

  let dexpr = dexpr_s Instructions.zero

  [%%inline_defs "Item.*"]
end
[@@add "subtype.ml"]

open Base
open Utils

module%inlined_contents Make
    (FA : Features.T
            with type raw_pointer = Features.Off.raw_pointer
             and type mutable_pointer = Features.Off.mutable_pointer) =
struct
  open Ast

  module FB = struct
    include FA
    include Features.On.Mutable_variable
    include Features.Off.Mutable_reference
  end

  include
    Phase_utils.MakeBase (FA) (FB)
      (struct
        let phase_id = Diagnostics.Phase.RefMut
      end)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module S = struct
      include Features.SUBTYPE.Id

      let mutable_variable = Fn.const Features.On.mutable_variable
    end

    module UA = Ast_utils.Make (FA)
    module UB = Ast_utils.Make (FB)

    let ( let* ) x f = Option.bind ~f x

    module Expr = struct
      let expect_mut_borrow (e : A.expr) : A.expr option =
        match e.e with A.Borrow { kind = Mut _; e; _ } -> Some e | _ -> None

      let expect_deref (e : A.expr) : A.expr option =
        match e.e with
        | App { f = { e = GlobalVar (`Primitive Deref); _ }; args = [ e ]; _ }
          ->
            Some e
        | _ -> None

      let expect_concrete_app1 (f : Concrete_ident.name) (e : A.expr) :
          A.expr option =
        match e.e with
        | App { f = { e = GlobalVar (`Concrete f') }; args = [ e ] }
          when Concrete_ident.eq_name f f' ->
            Some e
        | _ -> None

      let expect_deref_mut_app =
        expect_concrete_app1 Core__ops__deref__DerefMut__deref_mut

      let expect_local_var (e : A.expr) : A.expr option =
        match e.e with LocalVar i -> Some e | _ -> None
    end

    let deref_mut_allowed (t : A.ty) : bool =
      match t with
      | TApp { ident; _ } -> Global_ident.eq_name Alloc__vec__Vec ident
      | _ -> false

    let match_mut_borrow (e : A.expr) : A.expr option =
      let* e = Expr.expect_mut_borrow e in
      match Expr.expect_local_var e with
      | Some e -> Some e (* we have a `&mut x`, `x` is a local identifier *)
      | None -> (
          match
            let* e = Expr.expect_deref e in
            let* e = Expr.expect_deref_mut_app e in
            Expr.expect_mut_borrow e
          with
          | Some e ->
              (* we have a `&mut *(&mut x).deref_mut()` with x local id *)
              (* we allow this only for know "identity-like" instances of `deref_mut` *)
              if deref_mut_allowed e.typ then Some e else None
          | None ->
              (* We entered a `&mut`, but then we get an arbitrary
                 expression.  Since we reject every function call that
                 returns a `&mut`, that is fine *)
              Some e)

    [%%inline_defs dmutability]

    let rec dty (span : span) (ty : A.ty) : B.ty =
      match ty with
      | [%inline_arms "dty.*" - TRef] -> auto
      | TRef { mut = Mutable _; _ } ->
          Error.raise { kind = UnallowedMutRef; span }
      | TRef { witness; typ; mut = Immutable as mut; region } ->
          TRef { witness; typ = dty span typ; mut; region }

    and dborrow_kind (_span : span) (borrow_kind : A.borrow_kind) :
        B.borrow_kind =
      match borrow_kind with
      | [%inline_arms "dborrow_kind.*" - Mut] -> auto
      | Mut _ -> Shared

    and extract_direct_ref_mut (ty_span : span) (t : A.ty) (e : A.expr) :
        (B.ty * B.expr, B.ty * B.expr) Either.t =
      let e = UA.Mappers.normalize_borrow_mut#visit_expr () e in
      match match_mut_borrow e with
      | Some e ->
          let e = dexpr e in
          Either.First (e.typ, e)
      | _ -> Either.Second (dty ty_span t, dexpr e)

    and dexpr_unwrapped (expr : A.expr) : B.expr =
      let span = expr.span in
      match expr.e with
      | [%inline_arms "dexpr'.*" - App - Borrow] ->
          map (fun e -> B.{ e; typ = dty expr.span expr.typ; span = expr.span })
      | Borrow { kind; e; witness } ->
          {
            e =
              Borrow
                {
                  kind =
                    (match kind with
                    | Mut _ ->
                        Error.raise { kind = UnallowedMutRef; span = expr.span }
                    | Shared -> B.Shared
                    | Unique -> B.Unique);
                  e = dexpr e;
                  witness;
                };
            typ = dty expr.span expr.typ;
            span = expr.span;
          }
      | App { f; args } -> (
          match f.typ with
          | TArrow (input_types, type_output0) -> (
              let typed_inputs =
                match List.zip input_types args with
                | Ok args ->
                    List.map
                      ~f:(uncurry @@ extract_direct_ref_mut expr.span)
                      args
                | Unequal_lengths ->
                    Error.raise
                      {
                        kind =
                          AssertionFailure { details = "Bad arity application" };
                        span = expr.span;
                      }
              in
              if [%matches? A.TRef { mut = Mutable _; _ }] type_output0 then
                Error.raise { kind = UnallowedMutRef; span = expr.span };
              let ret_unit = UA.is_unit_typ type_output0 in
              let mut_typed_inputs =
                List.filter_map ~f:Either.First.to_option typed_inputs
              in
              let mut_input_types = List.map ~f:fst mut_typed_inputs in
              let type_output =
                UB.make_tuple_typ
                @@ Option.to_list
                     (if ret_unit then None
                     else Some (dty expr.span type_output0))
                @ mut_input_types
              in
              let f_typ =
                B.TArrow
                  ( List.map
                      ~f:(function First (t, _) | Second (t, _) -> t)
                      typed_inputs,
                    type_output )
              in
              let e =
                B.App
                  {
                    f =
                      {
                        (dexpr { f with typ = UA.unit_typ }) with
                        span = f.span;
                        typ = f_typ;
                      };
                    args =
                      List.map
                        ~f:(function First (_, e) | Second (_, e) -> e)
                        typed_inputs;
                  }
              in
              let expr = B.{ e; typ = type_output; span = expr.span } in
              let returned_value_ident =
                LocalIdent.
                  {
                    name = "todo_fresh_var";
                    id = LocalIdent.var_id_of_int (-1) (* todo *);
                  }
              in
              match mut_typed_inputs with
              | [ (_, e) ] when ret_unit -> (
                  match e.e with
                  | LocalVar var ->
                      {
                        expr with
                        typ = UB.unit_typ;
                        e =
                          B.Assign
                            {
                              lhs = LhsLocalVar { var; typ = e.typ };
                              witness = Features.On.mutable_variable;
                              e = expr;
                            };
                      }
                  | _ ->
                      UB.make_let
                        (UB.make_wild_pat e.typ e.span)
                        expr (UB.unit_expr e.span))
              | _ ->
                  let idents =
                    List.map
                      ~f:(fun (ty, e) ->
                        match e.e with
                        | LocalVar i ->
                            (* TODO, generate fresh variable here *)
                            let i_temp =
                              LocalIdent.{ i with name = i.name ^ "_temp" }
                            in
                            Either.First (ty, i, i_temp, e.span)
                        | _ -> Either.Second (ty, e.span))
                      mut_typed_inputs
                  in
                  let assigns =
                    List.map
                      ~f:(fun (typ, i, var, span) ->
                        {
                          expr with
                          typ = UB.unit_typ;
                          e =
                            B.Assign
                              {
                                lhs = LhsLocalVar { var = i; typ };
                                witness = Features.On.mutable_variable;
                                e = { typ; span; e = LocalVar var };
                              };
                        })
                      (List.filter_map ~f:Either.First.to_option idents)
                  in
                  UB.make_let
                    (UB.make_tuple_pat
                    @@ List.map ~f:(function
                         | Either.Second (typ, span) ->
                             UB.make_wild_pat typ span
                         | Either.First (typ, _, i_temp, span) ->
                             UB.make_var_pat i_temp typ span)
                    @@ Option.to_list
                         (if ret_unit then None
                         else
                           Some
                             (Either.First
                                ( dty expr.span type_output0,
                                  returned_value_ident,
                                  returned_value_ident,
                                  expr.span )))
                    @ idents)
                    expr
                  @@ List.fold_right
                       ~init:
                         (if ret_unit then UB.unit_expr expr.span
                         else
                           {
                             expr with
                             e = LocalVar returned_value_ident;
                             typ = dty expr.span type_output0;
                           })
                       ~f:UB.make_seq assigns)
          | _ ->
              Error.raise
                {
                  kind =
                    Unimplemented
                      { issue_id = Some 76; details = Some "Incomplete phase" };
                  span = expr.span;
                })
      [@@inline_ands bindings_of dexpr - dexpr']

    [%%inline_defs "Item.*"]

    (* [%%inline_defs "Item.*"] *)
  end

  include Implem
  module FA = FA
end
[@@add "subtype.ml"]

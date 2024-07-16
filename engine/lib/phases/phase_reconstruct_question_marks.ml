open! Prelude

module%inlined_contents Make (FA : Features.T) = struct
  open Ast

  module FB = struct
    include FA
    include Features.On.Question_mark
  end

  include
    Phase_utils.MakeBase (FA) (FB)
      (struct
        let phase_id = Diagnostics.Phase.ResugarQuestionMarks
      end)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module UA = Ast_utils.Make (FA)
    module UB = Ast_utils.Make (FB)

    module S = struct
      include Features.SUBTYPE.Id
      include Features.SUBTYPE.On.Question_mark
    end

    module QuestionMarks = struct
      [@@@warning "-9"]

      open A

      (** The types supported for [e] in a [e?] expression *)
      type qm_kind = QMResult of { success : ty; error : ty } | QMOption of ty

      (** Interpret a type [t] as a [qm_kind] *)
      let qm_kind_of_typ span (t : ty) : qm_kind =
        let is_result = Global_ident.eq_name Core__result__Result in
        let is_option = Global_ident.eq_name Core__option__Option in
        match t with
        | TApp { ident; args = [ GType s; GType e ] } when is_result ident ->
            QMResult { success = s; error = e }
        | TApp { ident; args = [ GType s ] } when is_option ident -> QMOption s
        | _ ->
            Error.assertion_failure span
              ("expected something of type Option<_> or Result<_, _>, instead, \
                got: "
              ^ [%show: ty] t)

      (** Expects [impl] to be an impl. expr. for the trait
      `std::ops::FromResidual` for the type [Result<_, _>], and
      extract its parent [From] impl expr *)
      let expect_residual_impl_result (impl : impl_expr) : impl_expr option =
        match impl with
        | ImplApp
            { impl = Concrete { trait; _ }; args = [ _; _; _; from_impl ] }
          when Concrete_ident.eq_name Core__result__Impl_27 trait ->
            Some from_impl
        | _ -> None

      (** Expects [t] to be [Result<S, E>], and returns [(S, E)] *)
      let expect_result_type (t : ty) : (ty * ty) option =
        match t with
        | TApp { ident; args = [ GType s; GType e ] }
          when Global_ident.eq_name Core__result__Result ident ->
            Some (s, e)
        | _ -> None

      (** Construct [Result<S,E>] *)
      let make_result_type (success : ty) (error : ty) : ty =
        let ident = Global_ident.of_name Type Core__result__Result in
        TApp { ident; args = [ GType success; GType error ] }

      (** Retype a [Err::<_, E>(x)] literal, as [Err::<success, E>(x)] *)
      let retype_err_literal (e : expr) (success : ty) (error : ty) =
        match e.e with
        | Construct { constructor; _ }
          when Global_ident.eq_name Core__result__Result__Err constructor ->
            { e with typ = make_result_type success error }
        | _ -> e

      (** [map_err e error_dest impl] creates the expression
      [e.map_err(from)] with the proper types and impl
      informations. *)
      let map_err (e : expr) (error_dest : ty) impl : expr option =
        let* success, error_src = expect_result_type e.typ in
        let* impl = expect_residual_impl_result impl in
        if [%equal: ty] error_src error_dest then Some e
        else
          let from_typ = TArrow ([ error_src ], error_dest) in
          let from =
            UA.call ~kind:(AssociatedItem Value) ~impl Core__convert__From__from
              [] e.span from_typ
          in
          let call =
            UA.call Core__result__Impl__map_err [ e; from ] e.span
              (make_result_type success error_dest)
          in
          Some call

      (** [extract e] returns [Some (x, ty)] if [e] was a `y?`
      desugared by rustc. `y` is `x` plus possibly a coercion. [ty] is
      the return type of the function. *)
      let extract (e : expr) : (expr * ty) option =
        let extract_return (e : expr) =
          match e.e with
          | Return
              {
                e =
                  {
                    e =
                      App
                        {
                          f = { e = GlobalVar f };
                          args = [ { e = LocalVar residual_var; _ } ];
                          trait = Some (impl, _);
                        };
                    typ = return_typ;
                    _;
                  };
                _;
              } ->
              Some (f, residual_var, return_typ, impl)
          | _ -> None
        in
        let extract_pat_app_bd (p : pat) : (global_ident * local_ident) option =
          match p.p with
          | PConstruct
              {
                name;
                args =
                  [
                    {
                      pat =
                        {
                          p =
                            PBinding { mut = Immutable; var; subpat = None; _ };
                          _;
                        };
                      _;
                    };
                  ];
                _;
              } ->
              Some (name, var)
          | _ -> None
        in
        match e.e with
        | Match
            {
              scrutinee =
                { e = App { f = { e = GlobalVar n; _ }; args = [ expr ] }; _ };
              arms =
                [
                  { arm = { arm_pat = pat_break; body }; _ };
                  {
                    arm =
                      {
                        arm_pat = pat_continue;
                        body = { e = LocalVar continue_var; _ };
                      };
                    _;
                  };
                ];
            }
        (*[@ocamlformat "disable"]*)
          when Global_ident.eq_name Core__ops__try_trait__Try__branch n ->
            let* body =
              UA.Expect.concrete_app1 Rust_primitives__hax__never_to_any body
            in
            let* f, residual_var, fun_return_typ, residual_impl =
              extract_return body
            in
            let* f_break, residual_var' = extract_pat_app_bd pat_break in
            let* f_continue, continue_var' = extract_pat_app_bd pat_continue in
            let*? _ = [%equal: local_ident] residual_var residual_var' in
            let*? _ = [%equal: local_ident] continue_var continue_var' in
            let*? _ =
              Global_ident.eq_name Core__ops__control_flow__ControlFlow__Break
                f_break
              && Global_ident.eq_name
                   Core__ops__control_flow__ControlFlow__Continue f_continue
              && Global_ident.eq_name
                   Core__ops__try_trait__FromResidual__from_residual f
            in
            let expr =
              let kind = qm_kind_of_typ e.span in
              match (kind expr.typ, kind fun_return_typ) with
              | ( QMResult { error = local_err; _ },
                  QMResult { error = return_err; _ } ) ->
                  let expr = retype_err_literal expr e.typ local_err in
                  map_err expr return_err residual_impl
                  |> Option.value ~default:expr
              | QMOption _, QMOption _ -> expr
              | _ ->
                  Error.assertion_failure e.span
                    "expected expr.typ and fun_return_typ to be both Options \
                     or both Results"
            in
            Some (expr, fun_return_typ)
        | _ -> None
    end

    [%%inline_defs dmutability]

    let rec dexpr_unwrapped (expr : A.expr) : B.expr =
      let h = [%inline_body dexpr_unwrapped] in
      match QuestionMarks.extract expr with
      | Some (e, return_typ) ->
          {
            e =
              QuestionMark
                {
                  e = dexpr e;
                  return_typ = dty e.span return_typ;
                  witness = Features.On.question_mark;
                };
            span = expr.span;
            typ = dty expr.span expr.typ;
          }
      | None -> h expr
      [@@inline_ands bindings_of dexpr]

    [%%inline_defs "Item.*"]
  end

  include Implem
  module FA = FA
end
[@@add "subtype.ml"]

(* module _ (F: Features.T): Phase_utils.PHASE = Make(F) *)

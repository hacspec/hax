open Base
open Utils

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

      let question_mark = Fn.const Features.On.question_mark
    end

    module QuestionMarks = struct
      [@@@warning "-9"]

      open A

      type t = {
        start : expr;
        end_ : expr;
        var : local_ident;
        var_typ : ty;
        body : expr;
        state : loop_state option;
        label : string option;
        witness : FA.loop;
      }
      [@@deriving show]

      let mk_core_ops path =
        `Concrete { crate = "core"; path = Non_empty_list.("ops" :: path) }

      let core_ops_try_branch = mk_core_ops [ "try_trait"; "Try"; "branch" ]
      let cf_break = mk_core_ops [ "control_flow"; "Break" ]
      let cf_continue = mk_core_ops [ "control_flow"; "Continue" ]

      let f_from_residual =
        mk_core_ops [ "try_trait"; "FromResidual"; "from_residual" ]

      let extract (e : expr) : (expr * ty) option =
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
                  {
                    arm =
                      {
                        arm_pat = pat_break;
                        body =
                          {
                            e =
                              Return
                                {
                                  e =
                                    {
                                      e =
                                        App
                                          {
                                            f = { e = GlobalVar f };
                                            args =
                                              [
                                                {
                                                  e = LocalVar residual_arg_var;
                                                  _;
                                                };
                                              ];
                                          };
                                      typ = converted_typ;
                                      _;
                                    };
                                  _;
                                };
                          };
                      };
                    _;
                  };
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
          when [%equal: global_ident] n core_ops_try_branch -> (
            match
              (extract_pat_app_bd pat_break, extract_pat_app_bd pat_continue)
            with
            | Some (f_break, residual_arg_var'), Some (f_continue, continue_var')
              when [%equal: global_ident] f_break cf_break
                   && [%equal: global_ident] f_continue cf_continue
                   && [%equal: global_ident] f f_from_residual
                   && [%equal: local_ident] residual_arg_var residual_arg_var'
                   && [%equal: local_ident] continue_var continue_var' ->
                Some (expr, converted_typ)
            | _ -> None)
        | _ -> None
    end

    [%%inline_defs dmutability]

    let rec dexpr_unwrapped (expr : A.expr) : B.expr =
      let h = [%inline_body dexpr_unwrapped] in
      match QuestionMarks.extract expr with
      | Some (e, converted_typ) ->
          {
            e =
              QuestionMark
                {
                  e = dexpr e;
                  converted_typ = dty e.span converted_typ;
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

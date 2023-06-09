open Base
open Utils

module%inlined_contents Make
    (FA : Features.T
    (* with type raw_pointer = Features.off *)
    (*  and type mutable_pointer = Features.off *)) =
struct
  open Ast

  module FB = struct
    include FA
    include Features.On.For_loop
  end

  include
    Phase_utils.MakeBase (FA) (FB)
      (struct
        let phase_id = Diagnostics.Phase.ResugarForLoops
      end)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module UA = Ast_utils.Make (FA)
    module UB = Ast_utils.Make (FB)

    module S = struct
      include Features.SUBTYPE.Id

      let for_loop = Fn.const Features.On.for_loop
    end

    module For = struct
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

      let extract (e : expr) : t option =
        let e = UA.Mappers.normalize_borrow_mut#visit_expr () e in
        match e.e with
        | Match
            {
              scrutinee =
                {
                  e =
                    App
                      {
                        f =
                          {
                            e =
                              GlobalVar
                                (`Concrete
                                  {
                                    crate = "core";
                                    path =
                                      Non_empty_list.
                                        [
                                          "iter";
                                          "traits";
                                          "collect";
                                          "IntoIterator";
                                          "into_iter";
                                        ];
                                  });
                          };
                        args =
                          [
                            {
                              e =
                                Construct
                                  {
                                    constructor =
                                      `Concrete
                                        {
                                          crate = "core";
                                          path =
                                            Non_empty_list.
                                              [ "ops"; "range"; "Range" ];
                                        };
                                    constructs_record = true;
                                    fields =
                                      [
                                        ( `Concrete
                                            {
                                              crate = "core";
                                              path =
                                                Non_empty_list.
                                                  [ "ops"; "range"; "start" ];
                                            },
                                          start );
                                        ( `Concrete
                                            {
                                              crate = "core";
                                              path =
                                                Non_empty_list.
                                                  [ "ops"; "range"; "finish" ];
                                            },
                                          end_ );
                                      ];
                                    base = None;
                                  };
                            };
                          ];
                      };
                };
              arms =
                [
                  {
                    arm =
                      {
                        arm_pat =
                          {
                            p =
                              PBinding
                                {
                                  mut = Mutable _;
                                  mode = ByValue;
                                  var = iter_variable;
                                  subpat = None;
                                };
                          };
                        body =
                          {
                            e =
                              Loop
                                {
                                  label;
                                  kind = UnconditionalLoop;
                                  state;
                                  witness;
                                  body =
                                    {
                                      e =
                                        Let
                                          {
                                            monadic = None;
                                            lhs = { p = PWild };
                                            rhs =
                                              {
                                                e =
                                                  Match
                                                    {
                                                      scrutinee =
                                                        {
                                                          e =
                                                            App
                                                              {
                                                                f =
                                                                  {
                                                                    e =
                                                                      GlobalVar
                                                                        (`Concrete
                                                                          {
                                                                            crate =
                                                                              "core";
                                                                            path =
                                                                              Non_empty_list.
                                                                                [
                                                                                "iter";
                                                                                "traits";
                                                                                "iterator";
                                                                                "Iterator";
                                                                                "next";
                                                                                ];
                                                                          });
                                                                  };
                                                                args =
                                                                  [
                                                                    {
                                                                      e =
                                                                        Borrow
                                                                          {
                                                                            kind =
                                                                              Mut
                                                                                _;
                                                                            e =
                                                                              {
                                                                                e =
                                                                                LocalVar
                                                                                next_iter_variable;
                                                                              };
                                                                          };
                                                                    };
                                                                  ];
                                                              };
                                                        };
                                                      arms =
                                                        [
                                                          {
                                                            arm =
                                                              {
                                                                arm_pat =
                                                                  {
                                                                    p =
                                                                      PConstruct
                                                                        {
                                                                          name =
                                                                            `Concrete
                                                                              {
                                                                                crate =
                                                                                "core";
                                                                                path =
                                                                                Non_empty_list.
                                                                                [
                                                                                "option";
                                                                                "None";
                                                                                ];
                                                                              };
                                                                          args =
                                                                            [];
                                                                          _;
                                                                        };
                                                                  };
                                                                body =
                                                                  {
                                                                    e =
                                                                      Break
                                                                        {
                                                                          e =
                                                                            {
                                                                              e =
                                                                                GlobalVar
                                                                                (`TupleCons
                                                                                0);
                                                                            };
                                                                        };
                                                                  };
                                                              };
                                                          };
                                                          {
                                                            arm =
                                                              {
                                                                arm_pat =
                                                                  {
                                                                    p =
                                                                      PConstruct
                                                                        {
                                                                          name =
                                                                            `Concrete
                                                                              {
                                                                                crate =
                                                                                "core";
                                                                                path =
                                                                                Non_empty_list.
                                                                                [
                                                                                "option";
                                                                                "Some";
                                                                                ];
                                                                              };
                                                                          args =
                                                                            [
                                                                              {
                                                                                pat =
                                                                                {
                                                                                p =
                                                                                PBinding
                                                                                {
                                                                                mut =
                                                                                Immutable;
                                                                                mode =
                                                                                ByValue;
                                                                                var;
                                                                                subpat =
                                                                                None;
                                                                                };
                                                                                typ =
                                                                                var_typ;
                                                                                };
                                                                              };
                                                                            ];
                                                                          _;
                                                                        };
                                                                  };
                                                                body =
                                                                  ( {
                                                                      e =
                                                                        Let
                                                                          {
                                                                            lhs =
                                                                              {
                                                                                p =
                                                                                PWild;
                                                                              };
                                                                            rhs =
                                                                              body;
                                                                            body =
                                                                              {
                                                                                e =
                                                                                GlobalVar
                                                                                (`TupleCons
                                                                                0);
                                                                              };
                                                                          };
                                                                    }
                                                                  | body );
                                                              };
                                                          };
                                                        ];
                                                    };
                                              };
                                            body =
                                              { e = GlobalVar (`TupleCons 0) };
                                          };
                                    };
                                  _;
                                };
                          };
                      };
                  };
                ];
            }
          when [%eq: local_ident] iter_variable next_iter_variable ->
            Some { start; end_; var; body; state; var_typ; label; witness }
        | _ -> None
               [@ocamlformat "disable"]
    end

    [%%inline_defs dmutability]

    let rec dexpr_unwrapped (expr : A.expr) : B.expr =
      let h = [%inline_body dexpr_unwrapped] in
      match For.extract expr with
      | Some { start; end_; var; body; label; state; var_typ; witness } ->
          {
            e =
              Loop
                {
                  body = dexpr body;
                  kind =
                    ForLoop
                      {
                        start = dexpr start;
                        end_ = dexpr end_;
                        var;
                        var_typ = dty expr.span var_typ;
                        witness = Features.On.for_loop;
                      };
                  state = Option.map ~f:(dloop_state expr.span) state;
                  label;
                  witness = S.loop witness;
                };
            span = expr.span;
            typ = UB.unit_typ;
          }
      | None -> h expr
      [@@inline_ands bindings_of dexpr]

    [%%inline_defs "Item.*"]
  end

  include Implem
  module FA = FA
end
[@@add "subtype.ml"]

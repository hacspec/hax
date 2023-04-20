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

  module A = Ast.Make (FA)
  module B = Ast.Make (FB)

  let metadata = Desugar_utils.Metadata.make ResugarForLoops

  module UA = Ast_utils.Make (FA)
  module UB = Ast_utils.Make (FB)
  include Desugar_utils.NoError

  module S = struct
    include Features.SUBTYPE.Id

    let for_loop = Fn.const Features.On.for_loop
  end

  module For = struct
    open A

    type t = {
      start : expr;
      end_ : expr;
      var : local_ident;
      body : expr;
      label : string option;
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
                                                [ "ops"; "range"; "end" ];
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
                      pat =
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
                                                              pat =
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
                                                              pat =
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
          Some { start; end_; var; body; label }
      | _ -> None
             [@ocamlformat "disable"]
  end

  [%%inline_defs dmutability + dty + dborrow_kind + dpat]

  let rec dexpr (expr : A.expr) : B.expr =
    let h = [%inline_body dexpr] in
    match For.extract expr with
    | Some { start; end_; var; body; label } ->
        {
          e =
            ForLoop
              {
                body = dexpr body;
                start = dexpr start;
                end_ = dexpr end_;
                var;
                label;
                witness = Features.On.for_loop;
              };
          span = expr.span;
          typ = UB.unit_typ;
        }
    | None -> h expr

  and dexpr' = [%inline_body dexpr']
  and darm = [%inline_body darm]
  and darm' = [%inline_body darm']
  and dlhs = [%inline_body dlhs]

  [%%inline_defs "Item.*"]

  module FA = FA
end
[@@add "subtype.ml"]

(* module _ (F: Features.T): Desugar_utils.DESUGAR = Make(F) *)

open Base
open Utils

module%inlined_contents Make (FA : Features.T) = struct
  open Ast

  module FB = struct
    include FA
    include Features.On.For_index_loop
  end

  include
    Phase_utils.MakeBase (FA) (FB)
      (struct
        let phase_id = Diagnostics.Phase.ResugarForIndexLoops
      end)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module UA = Ast_utils.Make (FA)
    module UB = Ast_utils.Make (FB)

    module S = struct
      include Features.SUBTYPE.Id

      let for_index_loop = Fn.const Features.On.for_index_loop
    end

    [%%inline_defs dmutability]

    let rec dloop_kind (span : span) (k : A.loop_kind) : B.loop_kind =
      match k with
      | ForLoop
          {
            it =
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
                typ;
                _;
              };
            pat =
              {
                p =
                  PBinding
                    { mut = Immutable; mode = ByValue; var; subpat = None };
                typ = _;
              };
            witness;
          } ->
          ForIndexLoop
            {
              start = dexpr start;
              end_ = dexpr end_;
              var;
              var_typ = dty span typ;
              witness = Features.On.for_index_loop;
            }
      | [%inline_arms "dloop_kind.*"] -> auto
      [@@inline_ands bindings_of dexpr]

    [%%inline_defs "Item.*"]
  end

  include Implem
  module FA = FA
end
[@@add "subtype.ml"]

open! Prelude
open! Ast

module%inlined_contents Make (F : Features.T) = struct
  open Ast
  module FA = F

  module FB = struct
    include F
    include Features.On.Quote
  end

  include
    Phase_utils.MakeBase (F) (FB)
      (struct
        let phase_id = Diagnostics.Phase.TransformHaxLibInline
      end)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module UA = Ast_utils.Make (F)
    module UB = Ast_utils.Make (FB)
    module Visitors = Ast_visitors.Make (FB)

    module S = struct
      module A = FA
      module B = FB
      include Features.SUBTYPE.Id

      let quote _ _ = Features.On.quote
    end

    [%%inline_defs dmutability]

    (** Patterns are "stored" in a
        [match None { Some <PAT> => (), _ => () }]
        dummy expression. *)
    let extract_pattern (e : B.expr) : B.pat option =
      match e.e with
      | Block
          ( {
              e =
                Match
                  {
                    arms =
                      [
                        {
                          arm =
                            {
                              arm_pat =
                                { p = PConstruct { args = [ arg ]; _ }; _ };
                              _;
                            };
                          _;
                        };
                        _;
                      ];
                    _;
                  };
              _;
            },
            _ ) ->
          Some arg.pat
      | _ -> None

    (** Extracts the first global_ident found in a pattern *)
    let first_global_ident (pat : B.pat) : global_ident option =
      UB.Reducers.collect_global_idents#visit_pat () pat |> Set.choose

    let rec dexpr' span (expr : A.expr') : B.expr' =
      match expr with
      | App { f = { e = GlobalVar f; _ }; args = [ payload ]; _ }
        when Global_ident.eq_name Hax_lib__inline f ->
          let bindings, str = dexpr payload |> UB.collect_let_bindings in
          let str =
            match
              UB.Expect.(block >> Option.bind ~f:borrow >> Option.bind ~f:deref)
                str
            with
            | Some { e = Literal (String str); _ } -> str
            | _ ->
                Error.assertion_failure span
                  "Malformed call to 'inline': cannot find string payload."
          in
          let code =
            List.map bindings ~f:(fun (pat, e) ->
                match
                  UB.Expect.pbinding_simple pat
                  |> Option.map ~f:(fun ((i, _) : Local_ident.t * _) -> i.name)
                with
                | Some "_constructor" ->
                    let id =
                      extract_pattern e
                      |> Option.bind ~f:first_global_ident
                      |> Option.value_exn
                    in
                    `Expr { e with e = GlobalVar id }
                | Some "_pat" ->
                    let pat = extract_pattern e |> Option.value_exn in
                    `Pat pat
                | _ -> `Expr e)
          in
          let verbatim = split_str ~on:"SPLIT_QUOTE" str in
          let contents =
            let rec f verbatim
                (code :
                  [ `Verbatim of string | `Expr of B.expr | `Pat of B.pat ] list)
                =
              match (verbatim, code) with
              | s :: s', code :: code' -> `Verbatim s :: code :: f s' code'
              | [ s ], [] -> [ `Verbatim s ]
              | [], [] -> []
              | _ ->
                  Error.assertion_failure span
                  @@ "Malformed call to 'inline'." ^ "\nverbatim="
                  ^ [%show: string list] verbatim
                  ^ "\ncode="
                  ^ [%show:
                      [ `Verbatim of string | `Expr of B.expr | `Pat of B.pat ]
                      list] code
            in
            f verbatim code
          in
          Quote { contents; witness = Features.On.quote }
      | [%inline_arms "dexpr'.*"] -> auto
      [@@inline_ands bindings_of dexpr - dexpr']

    [%%inline_defs "Item.*"]
  end

  include Implem
end
[@@add "subtype.ml"]

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
        let phase_id = [%auto_phase_name auto]
      end)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module UA = Ast_utils.Make (F)
    module UB = Ast_utils.Make (FB)
    module Visitors = Ast_visitors.Make (FB)
    module Attrs = Attr_payloads.Make (F) (Error)

    module S = struct
      module A = FA
      module B = FB
      include Features.SUBTYPE.Id

      let quote _ _ = Features.On.quote
    end

    [%%inline_defs dmutability + dsafety_kind]

    (** Patterns are "stored" in a
        [match None { Some <PAT> => (), _ => () }]
        dummy expression. *)
    let extract_pattern (e : B.expr) : B.pat option =
      match e.e with
      | Block
          {
            e =
              {
                e =
                  Match
                    {
                      arms =
                        [
                          {
                            arm =
                              {
                                arm_pat =
                                  { p = PConstruct { fields = [ arg ]; _ }; _ };
                                _;
                              };
                            _;
                          };
                          _;
                        ];
                      _;
                    };
                _;
              };
            _;
          } ->
          Some arg.pat
      | _ -> None

    (** Extracts the first global_ident found in a pattern *)
    let first_global_ident (pat : B.pat) : global_ident option =
      UB.Reducers.collect_global_idents#visit_pat () pat |> Set.choose

    let rec dexpr' span (expr : A.expr') : B.expr' =
      quote_of_expr' span expr
      |> Option.map ~f:(fun quote : B.expr' -> B.Quote quote)
      |> Option.value_or_thunk ~default:(fun _ ->
             [%inline_body dexpr'] span expr)

    and quote_of_expr (expr : A.expr) = quote_of_expr' expr.span expr.e

    and quote_of_expr' span (expr : A.expr') =
      match expr with
      | App { f = { e = GlobalVar f; _ }; args = [ payload ]; _ }
        when Global_ident.eq_name Hax_lib__inline f
             || Global_ident.eq_name Hax_lib__inline_unsafe f ->
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
                      |> Option.value_or_thunk ~default:(fun _ ->
                             Error.assertion_failure span
                               "Could not extract pattern (case constructor): \
                                this may be a bug in the quote macros in \
                                hax-lib.")
                    in
                    `Expr { e with e = GlobalVar id }
                | Some "_pat" ->
                    let pat =
                      extract_pattern e
                      |> Option.value_or_thunk ~default:(fun _ ->
                             Error.assertion_failure span
                               "Could not extract pattern (case pat): this may \
                                be a bug in the quote macros in hax-lib.")
                    in
                    `Pat pat
                | Some "_ty" ->
                    let typ =
                      match pat.typ with
                      | TApp { args = [ GType typ ]; _ } -> typ
                      | _ ->
                          Stdio.prerr_endline @@ "-pat->" ^ [%show: B.pat] pat;
                          Stdio.prerr_endline @@ "-expr->"
                          ^ [%show: B.expr'] e.e;
                          Error.assertion_failure span
                            "Malformed call to 'inline': expected type \
                             `Option<_>`."
                    in
                    `Typ typ
                | _ -> `Expr e)
          in
          let verbatim = split_str ~on:"SPLIT_QUOTE" str in
          let contents =
            let rec f verbatim
                (code :
                  [ `Verbatim of string
                  | `Expr of B.expr
                  | `Pat of B.pat
                  | `Typ of B.ty ]
                  list) =
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
                      [ `Verbatim of string
                      | `Expr of B.expr
                      | `Pat of B.pat
                      | `Typ of B.ty ]
                      list] code
            in
            f verbatim code
          in
          Some { contents; witness = Features.On.quote }
      | _ -> None
    [@@inline_ands bindings_of dexpr - dexpr']

    [%%inline_defs "Item.*" - ditems]

    let ditems items =
      let (module Attrs) = Attrs.with_items items in
      let f (item : A.item) =
        let before, after =
          let map_fst = List.map ~f:fst in
          try
            let replace = Attrs.late_skip item.attrs in
            Attrs.associated_items Attr_payloads.AssocRole.ItemQuote item.attrs
            |> List.map ~f:(fun assoc_item ->
                   let e : A.expr =
                     assoc_item |> Attrs.expect_fn |> Attrs.expect_expr
                   in
                   let quote =
                     UA.Expect.block e |> Option.value ~default:e
                     |> quote_of_expr
                     |> Option.value_or_thunk ~default:(fun _ ->
                            Error.assertion_failure assoc_item.span
                            @@ "Malformed `Quote` item: `quote_of_expr` \
                                failed. Expression was:\n"
                            (* ^ (UA.LiftToFullAst.expr e |> Print_rust.pexpr_str) *)
                            ^ [%show: A.expr] e)
                   in
                   let span = e.span in
                   let position, attr =
                     Attrs.find_unique_attr assoc_item.attrs ~f:(function
                       | ItemQuote q as attr -> Some (q.position, attr)
                       | _ -> None)
                     |> Option.value_or_thunk ~default:(fun _ ->
                            Error.assertion_failure assoc_item.span
                              "Malformed `Quote` item: could not find a \
                               ItemQuote payload")
                   in
                   let v : B.item' =
                     let origin : item_quote_origin =
                       {
                         item_kind = UA.kind_of_item item;
                         item_ident = item.ident;
                         position =
                           (if replace then `Replace
                            else
                              match position with
                              | After -> `After
                              | Before -> `Before);
                       }
                     in
                     Quote { quote; origin }
                   in
                   let attrs = [ Attr_payloads.to_attr attr assoc_item.span ] in
                   (B.{ v; span; ident = item.ident; attrs }, position))
            |> List.partition_tf ~f:(snd >> [%matches? Types.Before])
            |> map_fst *** map_fst
          with Diagnostics.SpanFreeError.Exn (Data (context, kind)) ->
            let error = Diagnostics.pretty_print_context_kind context kind in
            let msg = error in
            ([ B.make_hax_error_item item.span item.ident msg ], [])
        in
        before @ ditem item @ after
      in
      List.concat_map ~f items
  end

  include Implem
end
[@@add "subtype.ml"]

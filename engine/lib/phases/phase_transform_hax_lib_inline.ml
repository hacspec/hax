open! Prelude
open! Ast

module%inlined_contents Make (F : Features.T) = struct
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

    let counter = ref 0

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
          let code : B.quote_content list =
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
                    B.Expr { e with e = GlobalVar id }
                | Some "_pat" ->
                    let pat =
                      extract_pattern e
                      |> Option.value_or_thunk ~default:(fun _ ->
                             Error.assertion_failure span
                               "Could not extract pattern (case pat): this may \
                                be a bug in the quote macros in hax-lib.")
                    in
                    Pattern pat
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
                    Typ typ
                | _ -> Expr e)
          in
          let verbatim = split_str ~on:"SPLIT_QUOTE" str in
          let contents =
            let rec f verbatim (code : B.quote_content list) =
              match (verbatim, code) with
              | s :: s', code :: code' -> B.Verbatim s :: code :: f s' code'
              | [ s ], [] -> [ Verbatim s ]
              | [], [] -> []
              | _ ->
                  Error.assertion_failure span
                  @@ "Malformed call to 'inline'." ^ "\nverbatim="
                  ^ [%show: string list] verbatim
                  ^ "\ncode="
                  ^ [%show: B.quote_content list] code
            in
            f verbatim code
          in
          Some { contents; witness = Features.On.quote }
      | _ -> None
    [@@inline_ands bindings_of dexpr - dexpr']

    [%%inline_defs "Item.*" - ditems]

    let ditems items =
      let find_parent_item :
          Attr_payloads.UId.t -> (Attr_payloads.AssocRole.t * A.item) option =
        List.concat_map
          ~f:(fun (item : A.item) ->
            Attrs.raw_associated_item item.attrs
            |> List.map ~f:(fun (role, child_uid) -> (child_uid, (role, item))))
          items
        |> Map.of_alist_exn (module Attr_payloads.UId)
        |> Map.find
      in
      (* If [item] can be interpreted as a quote, return a `Quote` item *)
      let item_as_quote (item : A.item) =
        let* body =
          match item.v with
          | Fn { body = { e = Block { e; _ }; _ }; _ } -> Some e
          | _ -> None
        in
        let* uid = Attrs.uid item.attrs in
        let* role, _ = find_parent_item uid in
        let*? () = [%equal: Attr_payloads.AssocRole.t] ItemQuote role in
        let replace = Attrs.late_skip item.attrs in
        let* role =
          Attrs.find_unique_attr
            ~f:(function ItemQuote q -> Some q | _ -> None)
            item.attrs
        in
        let origin : item_quote_origin =
          {
            item_kind = UA.kind_of_item item;
            item_ident = item.ident;
            position =
              (if replace then `Replace
               else
                 match role.position with After -> `After | Before -> `Before);
          }
        in
        let quote =
          quote_of_expr body
          |> Option.value_or_thunk ~default:(fun _ ->
                 Error.assertion_failure item.span
                 @@ "Malformed `Quote` item: `quote_of_expr` failed. \
                     Expression was:\n"
                 ^ [%show: A.expr] body)
        in
        let attrs =
          let is_late_skip =
            [%matches? Types.ItemStatus (Included { late_skip = true })]
          in
          item.attrs |> Attr_payloads.payloads
          |> List.filter ~f:(fst >> is_late_skip >> not)
          |> List.map ~f:(fun (v, span) -> Attr_payloads.to_attr v span)
        in
        let A.{ span; ident; _ } = item in
        Some B.{ v = Quote { quote; origin }; span; ident; attrs }
      in
      (* Wraps [item_as_quote] to handle exns and fallback to the original item if the item is not a quote. *)
      let f i =
        try
          item_as_quote i
          |> Option.map ~f:(fun i -> [ i ])
          |> Option.value ~default:(ditem i)
        with Diagnostics.SpanFreeError.Exn (Data (context, kind)) ->
          let error = Diagnostics.pretty_print_context_kind context kind in
          let cast_item : A.item -> Ast.Full.item = Stdlib.Obj.magic in
          let ast = cast_item i |> Print_rust.pitem_str in
          let msg = error ^ "\nLast available AST for this item:\n\n" ^ ast in
          [ B.make_hax_error_item i.span i.ident msg ]
      in
      List.concat_map ~f items
  end

  include Implem
end
[@@add "subtype.ml"]

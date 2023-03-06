open Base
open Utils

module%inlined_contents Make
    (FA : Features.T
            with type raw_pointer = Features.off
             and type mutable_pointer = Features.off
    (* and type mutable_reference = Features.on *)) =
struct
  open Ast

  module FB = struct
    include FA
    include Features.On.Mutable_variable
    include Features.Off.Mutable_reference
  end

  module A = Ast.Make (FA)
  module B = Ast.Make (FB)

  module S = struct
    include Features.SUBTYPE.Id

    let mutable_variable = Fn.const ()
  end

  let metadata = Desugar_utils.Metadata.make "ref_mut"

  module UA = Ast_utils.Make (FA)
  module UB = Ast_utils.Make (FB)

  [%%inline_defs dmutability]

  type error =
    | IllegalRefMut of A.ty
    | BadArityApplication of A.expr
    | MutRefOutput of A.expr
  [@@deriving show]

  exception Error of error

  let raise e = raise (Error e)

  let rec dty (ty : A.ty) : B.ty =
    match ty with
    | [%inline_arms "dty.*" - TRef] -> auto
    | TRef { mut = Mutable _ } -> raise @@ IllegalRefMut ty
    | TRef { witness; typ; mut = Immutable as mut; region } ->
        TRef { witness; typ = dty typ; mut; region }

  and dgeneric_value = [%inline_body dgeneric_value]

  let dborrow_kind (borrow_kind : A.borrow_kind) : B.borrow_kind =
    match borrow_kind with
    | [%inline_arms "dborrow_kind.*" - Mut] -> auto
    | Mut witness -> Shared

  [%%inline_defs dpat]

  let rec extract_direct_ref_mut (t : A.ty) (e : A.expr) :
      (B.ty * (local_ident * B.ty * span), B.ty * B.expr) Either.t =
    let e = UA.Mappers.normalize_borrow_mut#visit_expr () e in
    match (t, e.e) with
    | ( A.TRef { witness; typ; mut = Mutable _; region },
        A.Borrow
          {
            kind = Mut _;
            e = { e = LocalVar i; typ = e_typ; span };
            witness = _;
          } ) ->
        let t = A.TRef { witness; typ; mut = Immutable; region } in
        Either.First (dty t, (i, dty e_typ, span))
    | _ -> Either.Second (dty t, dexpr e)

  and darm = [%inline_body darm]
  and darm' = [%inline_body darm']
  and dlhs = [%inline_body dlhs]

  and dexpr (expr : A.expr) : B.expr =
    match expr.e with
    | [%inline_arms "dexpr'.*" - App - Borrow] ->
        map (fun e -> B.{ e; typ = dty expr.typ; span = expr.span })
    | Borrow { kind; e; witness } ->
        {
          e =
            Borrow
              {
                kind =
                  (match kind with
                  | Mut _ -> failwith "TODO, illegal borrow"
                  | Shared -> B.Shared
                  | Unique -> B.Unique);
                e = dexpr e;
                witness;
              };
          typ = dty expr.typ;
          span = expr.span;
        }
    | App { f; args } -> (
        match f.typ with
        | TArrow (input_types, type_output0) -> (
            let typed_inputs =
              match List.zip input_types args with
              | Ok args -> List.map ~f:(uncurry extract_direct_ref_mut) args
              | Unequal_lengths -> raise @@ BadArityApplication expr
            in
            if [%matches? A.TRef { mut = Mutable _ }] type_output0 then
              raise @@ MutRefOutput f;
            let ret_unit = UA.is_unit_typ type_output0 in
            let mut_typed_inputs =
              List.filter_map ~f:Either.First.to_option typed_inputs
            in
            let mut_input_types = List.map ~f:fst mut_typed_inputs in
            let type_output =
              UB.make_tuple_typ
              @@ Option.to_list
                   (if ret_unit then None else Some (dty type_output0))
              @ mut_input_types
            in
            let f_typ =
              B.TArrow
                ( List.map
                    ~f:(function First (t, _) | Second (t, _) -> t)
                    typed_inputs,
                  type_output )
            in
            (* failwith @@ "ICI " ^ A.show_ty f.typ; *)
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
                      ~f:(function
                        | First (_, (i, typ, span)) ->
                            B.{ e = LocalVar i; typ; span }
                        | Second (_, e) -> e)
                      typed_inputs;
                }
            in
            let expr = B.{ e; typ = type_output; span = expr.span } in
            let returned_value_ident =
              LocalIdent.{ name = "todo_fresh_var"; id = 0 }
            in
            match mut_typed_inputs with
            | [ (_, (i, _, _)) ] when ret_unit ->
                {
                  expr with
                  typ = UB.unit_typ;
                  e = B.Assign { lhs = LhsLocalVar i; witness = (); e = expr };
                }
            | _ ->
                let idents =
                  List.map
                    ~f:(fun (ty, (i, _, span)) ->
                      (* TODO, generate fresh variable here *)
                      let i_temp =
                        LocalIdent.{ i with name = i.name ^ "_temp" }
                      in
                      (ty, i, i_temp, span))
                    mut_typed_inputs
                in
                let assigns =
                  List.map
                    ~f:(fun (typ, i, i_temp, span) ->
                      {
                        expr with
                        typ = UB.unit_typ;
                        e =
                          B.Assign
                            {
                              lhs = LhsLocalVar i;
                              witness = ();
                              e = { expr with typ; span; e = LocalVar i_temp };
                            };
                      })
                    idents
                in
                UB.make_let
                  (UB.make_tuple_pat
                  @@ List.map ~f:(fun (typ, _, i_temp, span) ->
                         UB.make_var_pat i_temp typ span)
                  @@ Option.to_list
                       (if ret_unit then None
                       else
                         Some
                           ( dty type_output0,
                             returned_value_ident,
                             returned_value_ident,
                             expr.span ))
                  @ idents)
                  expr
                @@ List.fold_right
                     ~init:
                       (if ret_unit then UB.unit_expr
                       else
                         {
                           expr with
                           e = LocalVar returned_value_ident;
                           typ = dty type_output0;
                         })
                     ~f:UB.make_seq assigns)
        | _ -> failwith @@ A.show_expr f)

  (* let ditem (x: A.item): B.item = failwith "todo"  *)
  [%%inline_defs "Item.*"]

  (* [%%inline_defs "Item.*"] *)
  module FA = FA
end
[@@add "subtype.ml"]

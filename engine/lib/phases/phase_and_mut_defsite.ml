open Base
open Utils

module%inlined_contents Make
    (FA : Features.T
            with type mutable_variable = Features.On.mutable_variable
             and type mutable_reference = Features.On.mutable_reference
             and type reference = Features.On.reference) =
struct
  open Ast
  module FB = FA

  include
    Phase_utils.MakeBase (FA) (FB)
      (struct
        let phase_id = Diagnostics.Phase.AndMutDefSite
      end)

  module A = Ast.Make (FA)
  module B = Ast.Make (FB)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module S = struct
      include Features.SUBTYPE.Id
    end

    module UB = Ast_utils.Make (FB)

    module M = struct
      open B
      open UB

      (* given `ty`, produces type `&mut ty` *)
      let mut_ref (typ : ty) : ty =
        let mut = Mutable Features.On.mutable_reference in
        TRef { witness = Features.On.reference; region = ""; typ; mut }

      (* given `e`, produces well-typed expr `&mut e` *)
      let mut_borrow (e : expr) : expr =
        let kind = Mut Features.On.mutable_reference in
        let witness = Features.On.reference in
        let e' = Borrow { kind; e; witness } in
        { e with e = e'; typ = mut_ref e.typ }

      let expect_mut_ref_param (param : param) :
          (local_ident * ty * span) option =
        let x = 0 in
        let* typ = Expect.mut_ref param.typ in
        match param.pat.p with
        | PBinding
            { mut = Immutable; mode = ByValue; var; typ = _; subpat = None } ->
            Some (var, typ, param.pat.span)
        | _ ->
            Error.unimplemented
              ~details:"Non-binding patterns for `&mut` inputs" param.pat.span

      let rewrite_fn_sig (params : param list) (output : ty) :
          (param list * ty * (local_ident * ty * span) list) option =
        let and_muts = List.filter_map ~f:expect_mut_ref_param params in
        match and_muts with
        | [] -> None
        | _ ->
            let params =
              List.map
                ~f:(fun param ->
                  match expect_mut_ref_param param with
                  | None -> param
                  | Some (var, typ, span) ->
                      let p : pat' =
                        let mut = Mutable Features.On.mutable_variable in
                        PBinding
                          { mut; mode = ByValue; var; typ; subpat = None }
                      in
                      { param with pat = { p; span; typ }; typ })
                params
            in
            let output_components =
              List.map ~f:snd3 and_muts
              @ if UB.is_unit_typ output then [] else [ output ]
            in
            let output = UB.make_tuple_typ output_components in
            Some (params, output, and_muts)

      (* visit an expression and replace all `Return e` nodes by `Return (f e)` *)
      let map_returns ~(f : expr -> expr) : expr -> expr =
        let visitor =
          object
            inherit [_] expr_map as super
            method visit_t () x = x
            method visit_mutability _ () m = m
            method visit_Return () e witness = Return { e = f e; witness }
          end
        in
        visitor#visit_expr ()

      (* transforms
          `(let … = … in)* expr`
         into
          `(let … = … in)* let output = expr in output` *)
      let wrap_in_identity_let (e : expr) : expr =
        let var = LocalIdent.{ id = var_id_of_int 0; name = "output" } in
        let f (e : expr) : expr =
          let lhs = UB.make_var_pat var e.typ e.span in
          let rhs = e in
          let body = { e with e = LocalVar var } in
          { body with e = Let { monadic = None; lhs; rhs; body } }
        in
        UB.map_body_of_nested_lets f e

      let mutref_to_mut_expr (vars : local_ident list) : expr -> expr =
        let ( <|?> ) (type a) (x : a option) (f : unit -> a option) : a option =
          x |> Option.map ~f:Option.some |> Option.value_or_thunk ~default:f
        in
        let in_vars = List.mem vars ~equal:[%equal: local_ident] in
        let expect_in_vars_local_var (x : expr) : local_ident option =
          match x.e with LocalVar v when in_vars v -> Some v | _ -> None
        in
        let retyped_local_var_in_vars e =
          let* var = expect_in_vars_local_var e in
          (* var is supposed to be typed `&mut _` *)
          let typ = Expect.mut_ref e.typ |> Option.value_exn in
          (* we reconstruct `e` to type it correctly *)
          Some { e = LocalVar var; typ; span = e.span }
        in
        let visitor =
          object
            inherit [_] expr_map as super
            method visit_t () x = x
            method visit_mutability _ () m = m

            method visit_expr () e =
              (let* e = Expect.deref e in
               retyped_local_var_in_vars e)
              <|?> (fun _ -> retyped_local_var_in_vars e)
              |> Option.value_or_thunk ~default:(fun _ -> super#visit_expr () e)
          end
        in
        visitor#visit_expr ()
    end

    include M

    let ditems (items : A.item list) : B.item list =
      let items : B.item list = Obj.magic items in
      let visitor =
        object
          inherit [_] B.item_map as super
          method visit_t () x = x
          method visit_mutability _ () m = m

          method visit_item' () item' =
            match item' with
            | Fn { name; generics; body; params } -> (
                match rewrite_fn_sig params body.typ with
                | Some (params, body_typ, vars) ->
                    let idents = List.map ~f:fst3 vars in
                    let vars =
                      List.map
                        ~f:(fun (var, typ, span) ->
                          B.{ span; typ; e = LocalVar var })
                        vars
                    in
                    let f (e : B.expr) : B.expr =
                      UB.make_tuple_expr ~span:e.span
                        (vars @ if UB.is_unit_typ e.typ then [] else [ e ])
                    in
                    let body =
                      body |> mutref_to_mut_expr idents |> map_returns ~f
                      |> wrap_in_identity_let
                      |> UB.map_body_of_nested_lets f
                    in
                    Fn { name; generics; body; params }
                | _ -> item')
            | _ -> super#visit_item' () item'
        end
      in
      List.map ~f:(visitor#visit_item ()) items

    let dexpr (e : A.expr) : B.expr =
      Caml.failwith "Should not be called directly"
  end

  include Implem
  module FA = FA
end
[@@add "subtype.ml"]

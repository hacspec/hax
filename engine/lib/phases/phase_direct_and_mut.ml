open Base
open Utils

module%inlined_contents Make
    (FA : Features.T
            with type raw_pointer = Features.Off.raw_pointer
             and type mutable_pointer = Features.Off.mutable_pointer) =
struct
  open Ast

  module FB = struct
    include FA
    include Features.On.Mutable_variable
    include Features.On.Arbitrary_lhs
    include Features.On.Nontrivial_lhs
    include Features.Off.Mutable_reference
  end

  include
    Phase_utils.MakeBase (FA) (FB)
      (struct
        let phase_id = Diagnostics.Phase.RefMut
      end)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module S = struct
      include Features.SUBTYPE.Id

      let mutable_variable = Fn.const Features.On.mutable_variable
      let nontrivial_lhs = Fn.const Features.On.nontrivial_lhs
      let arbitrary_lhs = Fn.const Features.On.arbitrary_lhs
    end

    module UA = Ast_utils.Make (FA)
    module UB = Ast_utils.Make (FB)

    let ( let* ) x f = Option.bind ~f x

    module Expr = struct
      let expect_mut_borrow (e : A.expr) : A.expr option =
        match e.e with A.Borrow { kind = Mut _; e; _ } -> Some e | _ -> None

      let expect_deref (e : A.expr) : A.expr option =
        match e.e with
        | App { f = { e = GlobalVar (`Primitive Deref); _ }; args = [ e ]; _ }
          ->
            Some e
        | _ -> None

      let expect_concrete_app1 (f : Concrete_ident.name) (e : A.expr) :
          A.expr option =
        match e.e with
        | App { f = { e = GlobalVar (`Concrete f') }; args = [ e ] }
          when Concrete_ident.eq_name f f' ->
            Some e
        | _ -> None

      let expect_deref_mut_app =
        expect_concrete_app1 Core__ops__deref__DerefMut__deref_mut

      let expect_local_var (e : A.expr) : A.expr option =
        match e.e with LocalVar i -> Some e | _ -> None
    end

    module Ty = struct
      let expect_arrow (typ : A.ty) : (A.ty list * A.ty) option =
        match typ with
        | TArrow (inputs, output) -> Some (inputs, output)
        | _ -> None

      let expect_arrow_b (typ : B.ty) : (B.ty list * B.ty) option =
        match typ with
        | TArrow (inputs, output) -> Some (inputs, output)
        | _ -> None

      let expect_mut_ref (typ : A.ty) : A.ty option =
        match typ with
        | TRef { mut = Mutable _; typ; _ } -> Some typ
        | _ -> None
    end

    module Place = struct
      open A

      type t = { place : place'; span : span; typ : ty }

      and place' =
        | LocalVar of LocalIdent.t
        | Deref of expr (* TODO: add Index, rename Proj in field acc. *)
        | IndexProjection of { place : t; index : expr }
        | FieldProjection of { place : t; projector : global_ident }
      [@@deriving show]

      let deref_mut_allowed (t : ty) : bool =
        match t with
        | TApp { ident; _ } -> Global_ident.eq_name Alloc__vec__Vec ident
        | _ -> false

      let rec of_expr (e : expr) : t option =
        let wrap place = Some { place; span = e.span; typ = e.typ } in
        match e.e with
        | App { f = { e = GlobalVar (`Primitive Deref); _ }; args = [ e ]; _ }
          -> (
            match of_expr e with
            | Some { place = IndexProjection _; _ } as value -> value
            | _ -> wrap @@ Deref e)
        | LocalVar i -> wrap @@ LocalVar i
        | App
            {
              f = { e = GlobalVar (`Projector _ as projector) };
              args = [ place ];
            } ->
            let* place = of_expr place in
            wrap @@ FieldProjection { place; projector }
        | App { f = { e = GlobalVar f }; args = [ place; index ] }
          when Global_ident.eq_name Core__ops__index__IndexMut__index_mut f ->
            (* Note that here, we allow any type to be `index_mut`ed:
               Hax translates that to `Rust_primitives.Hax.update_at`.
               This will typecheck IFF there is an implementation.
            *)
            let* typ = Ty.expect_mut_ref e.typ in
            let* place = Expr.expect_mut_borrow place in
            let* place = of_expr place in
            let place = IndexProjection { place; index } in
            Some { place; span = e.span; typ }
        | _ -> None

      let rec to_expr (p : t) : expr =
        let open UA in
        match p.place with
        | LocalVar v ->
            let e : expr' = LocalVar v in
            { e; typ = p.typ; span = p.span }
        | Deref e -> call' (`Primitive Deref) [ e ] p.span p.typ
        | FieldProjection { place; projector } ->
            let e = to_expr place in
            call' projector [ e ] p.span p.typ
        | IndexProjection { place; index } ->
            let e = to_expr place in
            call Core__ops__index__IndexMut__index_mut [ e; index ] p.span p.typ

      let expect_deref_mut (p : t) : t option =
        match p.place with
        | Deref e ->
            let* e = Expr.expect_deref_mut_app e in
            let* e = Expr.expect_mut_borrow e in
            of_expr e
        | _ -> None

      let expect_allowed_deref_mut (p : t) : t option =
        let* p = expect_deref_mut p in
        if deref_mut_allowed p.typ then Some p else None

      let skip_allowed_deref_mut (p : t) : t =
        Option.value ~default:p (expect_deref_mut p)
    end

    let expect_mut_borrow_of_place_or_pure_expr (e : A.expr) :
        (Place.t, A.expr) Either.t option =
      let e = UA.Mappers.normalize_borrow_mut#visit_expr () e in
      let* e = Expr.expect_mut_borrow e in
      Option.some
      @@
      match
        let* p = Place.of_expr e in
        Some (Place.skip_allowed_deref_mut p)
      with
      | Some place -> Either.First place
      | None -> Second e

    [%%inline_defs dmutability]

    let rec dty (span : span) (ty : A.ty) : B.ty =
      match ty with
      | [%inline_arms "dty.*" - TRef] -> auto
      | TRef { mut = Mutable _; _ } ->
          Error.raise { kind = UnallowedMutRef; span }
      | TRef { witness; typ; mut = Immutable as mut; region } ->
          TRef { witness; typ = dty span typ; mut; region }

    and dborrow_kind (_span : span) (borrow_kind : A.borrow_kind) :
        B.borrow_kind =
      match borrow_kind with
      | [%inline_arms "dborrow_kind.*" - Mut] -> auto
      | Mut _ -> Shared

    and place_to_lhs (p : Place.t) : B.lhs =
      let typ = dty p.span p.typ in
      match p.place with
      | LocalVar var -> LhsLocalVar { var; typ }
      | FieldProjection { place; projector } ->
          let e = place_to_lhs place in
          let field =
            match projector with
            | `Projector field -> (field :> global_ident)
            | _ ->
                Error.unimplemented
                  ~details:"try to borrow a projected tuple component?" p.span
          in
          LhsFieldAccessor
            { witness = Features.On.nontrivial_lhs; field; typ; e }
      | IndexProjection { place; index } ->
          let e = place_to_lhs place in
          let index = dexpr index in
          LhsArrayAccessor
            { e; typ; index; witness = Features.On.nontrivial_lhs }
      | _ ->
          let e = Place.to_expr p |> dexpr in
          LhsArbitraryExpr { witness = Features.On.arbitrary_lhs; e }

    and translate_app (f : A.expr) (raw_args : A.expr list) (span : span) :
        B.expr =
      let arg_types, otype =
        Ty.expect_arrow f.typ
        |> Option.value_or_thunk ~default:(fun _ ->
               Error.assertion_failure span "expected an arrow type here")
      in
      (* each input of `f` is either:
         - of type `&mut _` and then the value fed to f should either be a place or a "pure" expression;
         - of another type, and then the value can be anything.
      *)
      let args : ((Place.t, A.expr) Either.t * bool) list =
        (match List.zip arg_types raw_args with
        | Ok inputs -> inputs
        | _ -> Error.assertion_failure span "application: bad arity")
        |> List.map ~f:(fun (typ, (arg : A.expr)) ->
               if Ty.expect_mut_ref typ |> Option.is_some then
                 (* the argument of the function is mutable *)
                 let v =
                   expect_mut_borrow_of_place_or_pure_expr arg
                   |> Option.value_or_thunk ~default:(fun _ ->
                          Error.raise { kind = ExpectedMutRef; span = arg.span })
                 in
                 (v, true)
               else (Either.second arg, false))
      in
      (* `mutargs`: all mutable borrows fed to `f` *)
      let mutargs : (Place.t, A.expr) Either.t list =
        args |> List.filter ~f:snd |> List.map ~f:fst
      in
      match mutargs with
      | [] ->
          (* there is no mutation, we can reconstruct the expression right away *)
          let f, typ = (dexpr f, dty span otype) in
          let args = List.map ~f:dexpr raw_args in
          B.{ e = B.App { f; args }; typ; span }
      | _ -> (
          (* TODO: when LHS are better, compress `p1 = tmp1; ...; pN = tmpN` in `(p1...pN) = ...` *)
          (* we are generating:
             ```
             let (tmp1, …, tmpN, out) = ⟨f⟩(⟨…un-&mut args⟩);
             p1 = tmp1;
                 …
             pN = tmpN;
             out
             ```
          *)
          let ty_of_either : (Place.t, A.expr) Either.t -> A.ty = function
            | First p -> p.typ
            | Second e -> e.typ
          in
          let span_of_either : (Place.t, A.expr) Either.t -> span = function
            | First p -> p.span
            | Second e -> e.span
          in
          let b_ty_of_either : (Place.t, A.expr) Either.t -> B.ty = function
            | First p -> dty p.span p.typ
            | Second e -> dty e.span e.typ
          in

          let mutargs : ((local_ident * B.lhs) option * (B.ty * span)) list =
            let to_ident_lhs i = function
              | Either.First (place : Place.t) ->
                  let var =
                    LocalIdent.
                      { id = var_id_of_int 0; name = "tmp" ^ Int.to_string i }
                  in
                  Some (var, place_to_lhs place)
              | _ -> None
            in
            let to_ty_span x =
              let span = span_of_either x in
              (dty span (ty_of_either x), span)
            in
            List.mapi ~f:(fun i -> to_ident_lhs i &&& to_ty_span) mutargs
          in

          let out_var = LocalIdent.{ id = var_id_of_int 0; name = "out" } in
          let otype = dty f.span otype in
          let pat =
            let out =
              if UB.is_unit_typ otype then []
              else [ UB.make_var_pat out_var otype f.span ]
            in
            List.map
              ~f:(function
                | Some (var, _), (ty, span) -> UB.make_var_pat var ty span
                | None, (ty, span) -> UB.make_wild_pat ty span)
              mutargs
            @ out
            |> UB.make_tuple_pat
          in
          let f_call =
            let f : B.expr =
              let typ =
                B.TArrow (List.map ~f:(fst >> b_ty_of_either) args, pat.typ)
              in
              B.{ span = f.span; typ; e = dexpr' f.span f.e }
            in
            let unmut_args =
              args
              |> List.map
                   ~f:
                     (fst >> function
                      | Either.First p -> Place.to_expr p
                      | Either.Second e -> e)
              |> List.map ~f:dexpr
            in
            B.
              {
                e = App { f; args = unmut_args };
                typ = pat.typ;
                span = pat.span;
              }
          in
          (* when lhs type accepts tuple, assigns will be an option instead of a list *)
          let assigns =
            let flatten (o, meta) = Option.map o Fn.(id &&& const meta) in
            List.filter_map ~f:flatten mutargs
            |> List.map ~f:(fun ((var, lhs), (typ, span)) ->
                   let e = B.{ e = LocalVar var; span; typ } in
                   let witness = Features.On.mutable_variable in
                   B.{ e = Assign { lhs; e; witness }; span; typ = UB.unit_typ })
          in
          (* TODO: this should be greatly simplified when `lhs` type will accept tuples *)
          match assigns with
          | [ { e = Assign { lhs; witness; _ }; span; typ } ]
            when UB.is_unit_typ otype ->
              { e = Assign { lhs; e = f_call; witness }; span; typ }
          | _ ->
              let body =
                let init =
                  if UB.is_unit_typ otype then UB.unit_expr f.span
                  else B.{ typ = pat.typ; span = f.span; e = LocalVar out_var }
                in
                List.fold_right ~init ~f:UB.make_seq assigns
              in
              UB.make_let pat f_call body)

    and dexpr' (span : span) (e : A.expr') : B.expr' =
      match e with
      | [%inline_arms "dexpr'.*" - App - Borrow] -> auto
      | Borrow { kind; e; witness } ->
          Borrow
            {
              kind =
                (match kind with
                | Mut _ -> Error.raise { kind = UnallowedMutRef; span }
                | Shared -> B.Shared
                | Unique -> B.Unique);
              e = dexpr e;
              witness;
            }
      | App { f; args } -> (translate_app f args span).e

    and dexpr_unwrapped (e : A.expr) : B.expr =
      let span = e.span in
      let e' = dexpr' span e.e in
      match e' with
      | App { f; _ } ->
          let typ =
            Ty.expect_arrow_b f.typ
            |> Option.value_or_thunk ~default:(fun _ ->
                   Error.assertion_failure span "expected an arrow type here")
            |> snd
          in
          { e = e'; span; typ }
      | _ -> { e = e'; span; typ = dty e.span e.typ }
      [@@inline_ands bindings_of dexpr]

    [%%inline_defs "Item.*"]

    (* [%%inline_defs "Item.*"] *)
  end

  include Implem
  module FA = FA
end
[@@add "subtype.ml"]

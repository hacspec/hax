open! Prelude

module%inlined_contents Make (F : Features.T) = struct
  open Ast
  module FA = F

  module FB = struct
    include F
    include Features.Off.Nontrivial_lhs
    include Features.On.Construct_base
  end

  include
    Phase_utils.MakeBase (F) (FB)
      (struct
        let phase_id = Diagnostics.Phase.TrivializeAssignLhs
      end)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module S = struct
      include Features.SUBTYPE.Id
      include Features.SUBTYPE.On.Construct_base
    end

    module UA = Ast_utils.Make (F)
    module UB = Ast_utils.Make (FB)

    [%%inline_defs dmutability]

    let rec updater_of_lhs (lhs : A.lhs) (rhs : B.expr) (span : span) :
        (Local_ident.t * B.ty) option * B.expr =
      match lhs with
      | LhsLocalVar { var; typ } -> (Some (var, dty span typ), rhs)
      | LhsFieldAccessor { e; field; _ } -> (
          let lhs = UA.expr_of_lhs span e |> dexpr in
          match lhs.typ with
          | TApp { ident; _ } ->
              let rhs' =
                B.Construct
                  {
                    constructor = ident;
                    is_record = true (* TODO: might not be, actually *);
                    is_struct = true;
                    fields = [ (field, rhs) ];
                    base = Some (lhs, Features.On.construct_base);
                  }
              in
              let rhs = { B.e = rhs'; typ = lhs.typ; span } in
              updater_of_lhs e rhs span
          | _ -> Error.raise { kind = ArbitraryLHS; span })
      | LhsArrayAccessor { e; typ = _; index; _ } ->
          let lhs = UA.expr_of_lhs span e |> dexpr in
          let update_at : Concrete_ident.name =
            let typ =
              match lhs.typ with B.TRef { typ; _ } -> typ | typ -> typ
            in
            let is_array = [%matches? B.TArray _] typ in
            let is_slice = [%matches? B.TSlice _] typ in
            Stdio.prerr_endline @@ "typ=" ^ [%show: B.ty] typ;
            if is_array || is_slice then
              let h (arr : Concrete_ident.name) (slice : Concrete_ident.name) =
                if is_array then arr else slice
              in
              let index_typ =
                match index.typ with TRef { typ; _ } -> typ | typ -> typ
              in
              match index_typ with
              | TInt { size = SSize; signedness = Unsigned } ->
                  h
                    Rust_primitives__hax__monomorphized_update_at__update_array_at_usize
                    Rust_primitives__hax__monomorphized_update_at__update_slice_at_usize
              | TApp { ident; _ }
                when Global_ident.eq_name Core__ops__range__Range ident ->
                  h
                    Rust_primitives__hax__monomorphized_update_at__update_array_at_range
                    Rust_primitives__hax__monomorphized_update_at__update_slice_at_range
              | TApp { ident; _ }
                when Global_ident.eq_name Core__ops__range__RangeFrom ident ->
                  h
                    Rust_primitives__hax__monomorphized_update_at__update_array_at_range_from
                    Rust_primitives__hax__monomorphized_update_at__update_slice_at_range_from
              | TApp { ident; _ }
                when Global_ident.eq_name Core__ops__range__RangeTo ident ->
                  h
                    Rust_primitives__hax__monomorphized_update_at__update_array_at_range_to
                    Rust_primitives__hax__monomorphized_update_at__update_slice_at_range_to
              | TApp { ident; _ }
                when Global_ident.eq_name Core__ops__range__RangeFull ident ->
                  h
                    Rust_primitives__hax__monomorphized_update_at__update_array_at_range_full
                    Rust_primitives__hax__monomorphized_update_at__update_slice_at_range_full
              | _ -> Rust_primitives__hax__update_at
            else Rust_primitives__hax__update_at
          in
          let rhs =
            UB.call update_at
              [ lhs; dexpr index; rhs ]
              span (*lhs.typ*) UB.unit_typ
          in
          (None, rhs)
          (* updater_of_lhs e rhs span *)
      | LhsArbitraryExpr _ -> Error.raise { kind = ArbitraryLHS; span }

    and dexpr_unwrapped (expr : A.expr) : B.expr =
      let span = expr.span in
      match expr.e with
      | Assign { lhs; e; witness } -> (
          let bundle, e = updater_of_lhs lhs (dexpr e) expr.span in
          match bundle with
          | Some (var, typ) ->
              let lhs : B.lhs = LhsLocalVar { var; typ } in
              {
                e = Assign { lhs; e; witness };
                span = expr.span;
                typ = UB.unit_typ;
              }
          | None -> e)
      | [%inline_arms "dexpr'.*" - Assign] ->
          map (fun e -> B.{ e; typ = dty expr.span expr.typ; span = expr.span })
      [@@inline_ands bindings_of dexpr - dlhs - dexpr']

    [%%inline_defs "Item.*"]
  end

  include Implem
end
[@@add "subtype.ml"]

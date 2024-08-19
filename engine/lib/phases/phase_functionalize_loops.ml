open! Prelude

module%inlined_contents Make
    (F : Features.T
           with type continue = Features.Off.continue
            and type early_exit = Features.Off.early_exit) =
struct
  open Ast
  module FA = F

  module FB = struct
    include F
    include Features.Off.Loop
    include Features.Off.For_loop
    include Features.Off.While_loop
    include Features.Off.For_index_loop
    include Features.Off.State_passing_loop
  end

  include
    Phase_utils.MakeBase (F) (FB)
      (struct
        let phase_id = Diagnostics.Phase.FunctionalizeLoops
      end)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module UA = Ast_utils.Make (F)
    module UB = Ast_utils.Make (FB)

    module S = struct
      include Features.SUBTYPE.Id
    end

    type body_and_invariant = { body : B.expr; invariant : B.expr option }

    let extract_loop_invariant (body : B.expr) : body_and_invariant =
      match body.e with
      | Let
          {
            monadic = None;
            lhs = { p = PWild; _ };
            rhs =
              {
                e = App { f = { e = GlobalVar f; _ }; args = [ invariant ]; _ };
                _;
              };
            body;
          }
        when Global_ident.eq_name Hax_lib___internal_loop_invariant f ->
          { body; invariant = Some invariant }
      | _ -> { body; invariant = None }

    type iterator =
      | Range of { start : B.expr; end_ : B.expr }
      | Slice of B.expr
      | ChunksExact of { size : B.expr; slice : B.expr }
      | Enumerate of iterator
      | StepBy of { n : B.expr; it : iterator }
    [@@deriving show]

    let rec as_iterator (e : B.expr) : iterator option =
      match e.e with
      | Construct
          {
            constructor = `Concrete range_ctor;
            is_record = true;
            is_struct = true;
            fields =
              [ (`Concrete start_field, start); (`Concrete end_field, end_) ];
            base = None;
          }
        when Concrete_ident.eq_name Core__ops__range__Range__start start_field
             && Concrete_ident.eq_name Core__ops__range__Range range_ctor
             && Concrete_ident.eq_name Core__ops__range__Range__end end_field ->
          Some (Range { start; end_ })
      | _ -> meth_as_iterator e

    and meth_as_iterator (e : B.expr) : iterator option =
      let* f, args =
        match e.e with
        | App { f = { e = GlobalVar f; _ }; args; _ } -> Some (f, args)
        | _ -> None
      in
      let f_eq n = Global_ident.eq_name n f in
      let one_arg () = match args with [ x ] -> Some x | _ -> None in
      let two_args () = match args with [ x; y ] -> Some (x, y) | _ -> None in
      if f_eq Core__iter__traits__iterator__Iterator__step_by then
        let* it, n = two_args () in
        let* it = as_iterator it in
        Some (StepBy { n; it })
      else if
        f_eq Core__iter__traits__collect__IntoIterator__into_iter
        || f_eq Core__slice__Impl__iter
      then
        let* iterable = one_arg () in
        match iterable.typ with
        | TSlice _ -> Some (Slice iterable)
        | _ -> as_iterator iterable
      else if f_eq Core__iter__traits__iterator__Iterator__enumerate then
        let* iterable = one_arg () in
        let* iterator = as_iterator iterable in
        Some (Enumerate iterator)
      else if f_eq Core__slice__Impl__chunks_exact then
        let* slice, size = two_args () in
        Some (ChunksExact { size; slice })
      else None

    let fn_args_of_iterator (it : iterator) :
        (Concrete_ident.name * B.expr list) option =
      let open Concrete_ident_generated in
      match it with
      | Enumerate (ChunksExact { size; slice }) ->
          Some
            ( Rust_primitives__hax__folds__fold_enumerated_chunked_slice,
              [ size; slice ] )
      | Enumerate (Slice slice) ->
          Some (Rust_primitives__hax__folds__fold_enumerated_slice, [ slice ])
      | StepBy { n; it = Range { start; end_ } } ->
          Some
            (Rust_primitives__hax__folds__fold_range_step_by, [ start; end_; n ])
      | _ -> None

    [%%inline_defs dmutability]

    let rec dexpr_unwrapped (expr : A.expr) : B.expr =
      let span = expr.span in
      match expr.e with
      | Loop
          {
            body;
            kind = ForLoop { it; pat; _ };
            state = Some { init; bpat; _ };
            _;
          } ->
          let body = dexpr body in
          let { body; invariant } = extract_loop_invariant body in
          let it = dexpr it in
          let pat = dpat pat in
          let bpat = dpat bpat in
          let as_lhs_closure e : B.expr =
            {
              e = Closure { params = [ bpat; pat ]; body = e; captures = [] };
              typ = TArrow ([ bpat.typ; pat.typ ], e.typ);
              span = e.span;
            }
          in
          let fn : B.expr = as_lhs_closure body in
          let invariant : B.expr =
            let default : B.expr =
              { e = Literal (Bool true); typ = TBool; span = expr.span }
            in
            Option.value ~default invariant |> as_lhs_closure
          in
          let init = dexpr init in
          let f, args =
            match as_iterator it |> Option.bind ~f:fn_args_of_iterator with
            | Some (f, args) -> (f, args @ [ init; invariant; fn ])
            | None ->
                (Core__iter__traits__iterator__Iterator__fold, [ it; init; fn ])
          in
          UB.call ~kind:(AssociatedItem Value) f args span (dty span expr.typ)
      | Loop
          {
            body;
            kind = WhileLoop { condition; _ };
            state = Some { init; bpat; _ };
            _;
          } ->
          let body = dexpr body in
          let condition = dexpr condition in
          let bpat = dpat bpat in
          let init = dexpr init in
          let condition : B.expr =
            let e : B.expr' =
              Closure { params = [ bpat ]; body = condition; captures = [] }
            in
            let typ : B.ty = TArrow ([ bpat.typ ], condition.typ) in
            let span = condition.span in
            { e; typ; span }
          in
          let body : B.expr =
            let e : B.expr' =
              Closure { params = [ bpat ]; body; captures = [] }
            in
            let typ : B.ty = TArrow ([ bpat.typ ], body.typ) in
            let span = body.span in
            { e; typ; span }
          in
          UB.call ~kind:(AssociatedItem Value) Rust_primitives__hax__while_loop
            [ condition; init; body ] span (dty span expr.typ)
      | Loop { state = None; _ } ->
          Error.unimplemented ~details:"Loop without mutation?" span
      | Loop _ ->
          Error.unimplemented
            ~details:"Only for loop are being functionalized for now" span
      | Break _ ->
          Error.unimplemented
            ~details:
              "For now, the AST node [Break] is feature gated only by [loop], \
               there is nothing for having loops but no breaks."
            span
      | [%inline_arms "dexpr'.*" - Loop - Break - Continue - Return] ->
          map (fun e -> B.{ e; typ = dty expr.span expr.typ; span = expr.span })
      | _ -> .
      [@@inline_ands bindings_of dexpr - dexpr' - dloop_kind - dloop_state]

    [%%inline_defs "Item.*"]
  end

  include Implem
end
[@@add "subtype.ml"]

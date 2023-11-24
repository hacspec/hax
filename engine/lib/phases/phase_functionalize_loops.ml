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

    module ItExpr = struct
      open A

      type kind =
        | Range of { min : expr; max : expr }
        (* | Enumerate of t *)
        (* | Zip of t * t *)
        (* | ChunksExact of { it : t; size : expr } *)
        | Indexable of expr  (** a slice, an array *)

      and t = { kind : kind; typ : ty }

      module Expect = struct
        include UA.Expect

        let ( <|> ) (type a b) (f : a -> b option) (g : a -> b option) x =
          match f x with Some r -> Some r | None -> g x

        let any_ref (typ : ty) : ty option =
          match typ with TRef { typ; _ } -> Some typ | _ -> None

        let array (typ : ty) : ty option =
          match typ with TArray { typ; _ } -> Some typ | _ -> None

        let slice (typ : ty) : ty option =
          match typ with TSlice { ty; _ } -> Some ty | _ -> None

        let into_iter : expr -> expr option =
         fun e ->
          concrete_app1 Core__iter__traits__collect__IntoIterator__into_iter e

        let concrete_app_n (f : Concrete_ident.name) (e : expr) :
            expr list option =
          match e.e with
          | App { f = { e = GlobalVar (`Concrete f'); _ }; args; _ }
            when Concrete_ident.eq_name f f' ->
              Some args
          | _ -> None

        let concrete_app2 (f : Concrete_ident.name) (e : expr) :
            (expr * expr) option =
          match concrete_app_n f e with
          | Some [ x; y ] -> Some (x, y)
          | _ -> None

        let indexable (e : expr) : t option =
          let* e = into_iter e in
          let* typ =
            any_ref e.typ |> Option.value ~default:e.typ |> (array <|> slice)
          in
          Some { kind = Indexable e; typ }

        let range (e : expr) : t option =
          let* e = into_iter e in
          let* min, max = concrete_app2 Core__ops__range__Range e in
          Some { kind = Range { min; max }; typ = min.typ }
      end
    end

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
          let it = dexpr it in
          let pat = dpat pat in
          let bpat = dpat bpat in
          let fn : B.expr' =
            Closure { params = [ bpat; pat ]; body; captures = [] }
          in
          let fn : B.expr =
            {
              e = fn;
              typ = TArrow ([ bpat.typ; pat.typ ], body.typ);
              span = body.span;
            }
          in
          UB.call ~kind:(AssociatedItem Value)
            Core__iter__traits__iterator__Iterator__fold
            [ it; dexpr init; fn ]
            span (dty span expr.typ)
      | Loop
          {
            body;
            kind = ForIndexLoop { start; end_; var = var, var_typ, var_span; _ };
            state = None;
            _;
          } ->
          let var_typ = dty var_span var_typ in
          let body = dexpr body in
          let fn : B.expr =
            let e : B.expr' =
              let arg = UB.make_var_pat var var_typ var_span in
              Closure { params = [ arg ]; body; captures = [] }
            in
            let typ = B.TArrow ([ var_typ ], body.typ) in
            { e; typ; span = body.span }
          in
          UB.call ~kind:(AssociatedItem Value) Rust_primitives__hax__for_loop
            [ dexpr start; dexpr end_; fn ]
            span (dty span expr.typ)
      | Loop { state = None; _ } as hey ->
          Stdio.prerr_endline @@ ">>>" ^ [%show: A.expr'] hey;
            Error.unimplemented
            ~details:"Loop without mutation?HERE" span
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

open! Prelude

module%inlined_contents Make
    (F : Features.T
           with type monadic_action = Features.Off.monadic_action
            and type monadic_binding = Features.Off.monadic_binding) =
struct
  open Ast
  module FA = F

  module FB = struct
    include F
    include Features.Off.Continue
    include Features.Off.Early_exit
    include Features.Off.Question_mark
    include Features.Off.Break
    include Features.On.Monadic_binding
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

    module S = struct
      module A = FA
      module B = FB
      include Features.SUBTYPE.Id

      let monadic_binding _ = Features.On.monadic_binding
    end

    [%%inline_defs dmutability + dsafety_kind]

    module KnownMonads = struct
      type t = { monad : B.supported_monads option; typ : B.ty }
      [@@deriving show, eq]
      (** types of computations *)
      (* | MId of { typ : B.ty } *)
      (* | MReturn of { return : B.ty; continue : B.ty } *)

      (** translate a computation type to a simple type *)
      let to_typ (x : t) : B.ty =
        match x.monad with
        | None -> x.typ
        | Some (MResult err) ->
            let args = List.map ~f:(fun t -> B.GType t) [ x.typ; err ] in
            let ident =
              Global_ident.of_name ~value:false Core__result__Result
            in
            TApp { ident; args }
        | Some MOption ->
            let args = List.map ~f:(fun t -> B.GType t) [ x.typ ] in
            let ident =
              Global_ident.of_name ~value:false Core__option__Option
            in
            TApp { ident; args }
        | Some (MException return) ->
            let args = List.map ~f:(fun t -> B.GType t) [ return; x.typ ] in
            let ident =
              Global_ident.of_name ~value:false
                Core__ops__control_flow__ControlFlow
            in
            TApp { ident; args }

      let from_typ' : B.ty -> t = function
        | TApp { ident; args = [ GType return; GType continue ] }
          when Global_ident.eq_name Core__ops__control_flow__ControlFlow ident
          ->
            { monad = Some (MException return); typ = continue }
        | TApp { ident; args = [ GType ok; GType err ] }
          when Global_ident.eq_name Core__result__Result ident ->
            { monad = Some (MResult err); typ = ok }
        | TApp { ident; args = [ GType ok ] }
          when Global_ident.eq_name Core__option__Option ident ->
            { monad = Some MOption; typ = ok }
        | typ -> { monad = None; typ }

      (** the type of pure expression we can return in the monad *)
      let pure_type (x : t) = x.typ

      let lift details (e : B.expr) monad_of_e monad_destination : B.expr =
        match (monad_of_e, monad_destination) with
        | m1, m2 when [%equal: B.supported_monads option] m1 m2 -> e
        | None, Some (B.MResult _) ->
            UB.call_Constructor Core__result__Result__Ok false [ e ] e.span
              (to_typ { monad = monad_destination; typ = e.typ })
        | None, Some B.MOption ->
            UB.call_Constructor Core__option__Option__Some false [ e ] e.span
              (to_typ { monad = monad_destination; typ = e.typ })
        | _, Some (B.MException _) ->
            UB.call_Constructor Core__ops__control_flow__ControlFlow__Continue
              false [ e ] e.span
              (to_typ { monad = monad_destination; typ = e.typ })
        | m1, m2 ->
            Error.assertion_failure e.span
            @@ "Cannot lift from monad ["
            ^ [%show: B.supported_monads option] m1
            ^ "] to monad ["
            ^ [%show: B.supported_monads option] m2
            ^ "]" ^ "\n Details: " ^ details

      let lub span m1 m2 =
        match (m1, m2) with
        | None, m | m, None -> m
        | Some m1, Some m2 ->
            let impossible () =
              Error.assertion_failure span
              @@ "Trying to compute the lub of two incompatible monads:"
              ^ "\n • "
              ^ [%show: B.supported_monads] m1
              ^ "\n • "
              ^ [%show: B.supported_monads] m2
            in
            Option.some
              (match (m1, m2) with
              | (B.MResult _ | B.MOption), (B.MException _ as m)
              | (B.MException _ as m), (B.MResult _ | B.MOption) ->
                  m
              | B.MResult _, B.MResult _
              | B.MOption, B.MOption
              | B.MException _, B.MException _ ->
                  m1
              | B.MResult _, B.MOption | B.MOption, B.MResult _ -> impossible ())

      (** after transformation, are we **getting** inside a monad? *)
      let from_typ dty (old : A.ty) (new_ : B.ty) : t =
        let old = dty Span.default (* irrelevant *) old in
        let monad = from_typ' new_ in
        if B.equal_ty (pure_type monad) old then monad
        else { monad = None; typ = new_ }
    end

    let rec dexpr_unwrapped (expr : A.expr) : B.expr =
      let span = expr.span in
      let typ = dty span expr.typ in
      match expr.e with
      | Let { monadic = Some _; _ } -> .
      | Let { monadic = None; lhs; rhs; body } -> (
          let body' = dexpr body in
          let rhs' = dexpr rhs in
          let mrhs = KnownMonads.from_typ dty rhs.typ rhs'.typ in
          let lhs = { (dpat lhs) with typ = KnownMonads.pure_type mrhs } in
          match mrhs with
          | { monad = None; _ } ->
              let monadic = None in
              let rhs = rhs' in
              let body = body' in
              { e = Let { monadic; lhs; rhs; body }; span; typ = body.typ }
          | _ ->
              let mbody = KnownMonads.from_typ dty body.typ body'.typ in
              let m = KnownMonads.lub span mbody.monad mrhs.monad in
              let body = KnownMonads.lift "Let:body" body' mbody.monad m in
              let rhs = KnownMonads.lift "Let:rhs" rhs' mrhs.monad m in
              let monadic =
                match m with
                | None -> None
                | Some m -> Some (m, Features.On.monadic_binding)
              in
              { e = Let { monadic; lhs; rhs; body }; span; typ = body.typ })
      | Match { scrutinee; arms } ->
          let arms =
            List.map
              ~f:(fun { arm = { arm_pat; body = a; guard }; span } ->
                let b = dexpr a in
                let m = KnownMonads.from_typ dty a.typ b.typ in
                let g = Option.map ~f:dguard guard in
                (m, (dpat arm_pat, span, b, g)))
              arms
          in
          let arms =
            if List.is_empty arms then []
            else
              let m =
                List.map ~f:(fun ({ monad; _ }, _) -> monad) arms
                |> List.reduce_exn ~f:(KnownMonads.lub span)
              in
              List.map
                ~f:(fun (mself, (arm_pat, span, body, guard)) ->
                  let body = KnownMonads.lift "Match" body mself.monad m in
                  let arm_pat = { arm_pat with typ = body.typ } in
                  ({ arm = { arm_pat; body; guard }; span } : B.arm))
                arms
          in
          let typ =
            match arms with [] -> UB.never_typ | hd :: _ -> hd.arm.body.typ
          in
          { e = Match { scrutinee = dexpr scrutinee; arms }; span; typ }
      | If { cond; then_; else_ } ->
          let cond = dexpr cond in
          let then' = dexpr then_ in
          let else' = Option.map ~f:dexpr else_ in
          let mthen = KnownMonads.from_typ dty then_.typ then'.typ in
          let melse =
            match (else_, else') with
            | Some else_, Some else' ->
                KnownMonads.from_typ dty else_.typ else'.typ
            | _ -> mthen
          in
          let m = KnownMonads.lub span mthen.monad melse.monad in
          let else_ =
            Option.map
              ~f:(fun else' ->
                KnownMonads.lift "If:else-branch" else' melse.monad m)
              else'
          in
          let then_ = KnownMonads.lift "If:then-branch" then' mthen.monad m in
          { e = If { cond; then_; else_ }; span; typ = then_.typ }
      | Continue _ ->
          Error.unimplemented ~issue_id:15
            ~details:"TODO: Monad for loop-related control flow" span
      | Break _ ->
          Error.unimplemented ~issue_id:15
            ~details:"TODO: Monad for loop-related control flow" span
      | QuestionMark { e; _ } -> dexpr e
      | Return { e; _ } ->
          let open KnownMonads in
          let e = dexpr e in
          UB.call_Constructor Core__ops__control_flow__ControlFlow__Break false
            [ e ] span
            (to_typ @@ { monad = Some (MException e.typ); typ })
      | [%inline_arms
          "dexpr'.*" - Let - Match - If - Continue - Break - QuestionMark
          - Return] ->
          map (fun e -> B.{ e; typ = dty expr.span expr.typ; span = expr.span })

    and lift_if_necessary (e : B.expr) (target_type : B.ty) =
      if B.equal_ty e.typ target_type then e
      else
        UB.call Rust_primitives__hax__control_flow_monad__ControlFlowMonad__lift
          [ e ] e.span target_type
    [@@inline_ands bindings_of dexpr - dexpr']

    module Item = struct
      module OverrideDExpr = struct
        let dexpr (e : A.expr) : B.expr =
          let e' = dexpr e in
          match KnownMonads.from_typ dty e.typ e'.typ with
          | { monad = Some m; typ } ->
              UB.call
                (match m with
                | MException _ ->
                    Rust_primitives__hax__control_flow_monad__mexception__run
                | MResult _ ->
                    Rust_primitives__hax__control_flow_monad__mresult__run
                | MOption ->
                    Rust_primitives__hax__control_flow_monad__moption__run)
                [ e' ] e.span typ
          | _ -> e'
      end

      open OverrideDExpr

      [%%inline_defs "Item.*"]
    end

    include Item
  end

  include Implem
end
[@@add "subtype.ml"]

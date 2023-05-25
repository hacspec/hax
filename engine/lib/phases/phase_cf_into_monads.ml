open Base
open Utils

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

    (* TODO: when break is introduced: include Features.Off.Break *)
    include Features.On.Monadic_binding
  end

  module A = Ast.Make (F)
  module B = Ast.Make (FB)
  module ImplemT = Phase_utils.MakePhaseImplemT (A) (B)

  module Implem : ImplemT.T = struct
    module UA = Ast_utils.Make (F)
    module UB = Ast_utils.Make (FB)
    include Phase_utils.DefaultError

    module S = struct
      include Features.SUBTYPE.Id

      let monadic_binding _ = Features.On.monadic_binding
    end

    let metadata = Phase_utils.Metadata.make CfIntoMonads

    [%%inline_defs dmutability + dty + dborrow_kind + dpat]

    module KnownMonads = struct
      type t = { monad : B.supported_monads option; typ : B.ty }
      [@@deriving show, eq]
      (** types of computations *)
      (* | MId of { typ : B.ty } *)
      (* | MReturn of { return : B.ty; continue : B.ty } *)

      let std_ops_control_flow_mk l =
        `Concrete
          { crate = "std"; path = Non_empty_list.("ops" :: "ControlFlow" :: l) }

      let std_result_mk l =
        `Concrete
          { crate = "core"; path = Non_empty_list.("result" :: "Result" :: l) }

      let std_option_mk l =
        `Concrete
          { crate = "core"; path = Non_empty_list.("option" :: "Option" :: l) }

      let std_ops_control_flow = std_ops_control_flow_mk []

      (** translate a computation type to a simple type *)
      let to_typ (x : t) : B.ty =
        match x.monad with
        | None -> x.typ
        | Some (MResult err) ->
            let args = List.map ~f:(fun t -> B.GType t) [ x.typ; err ] in
            TApp { ident = std_result_mk []; args }
        | Some MOption ->
            let args = List.map ~f:(fun t -> B.GType t) [ x.typ ] in
            TApp { ident = std_option_mk []; args }
        | Some (MException return) ->
            let args = List.map ~f:(fun t -> B.GType t) [ return; x.typ ] in
            TApp { ident = std_ops_control_flow; args }

      let from_typ' : B.ty -> t = function
        | TApp { ident; args = [ GType return; GType continue ] }
          when GlobalIdent.equal ident std_ops_control_flow ->
            { monad = Some (MException return); typ = continue }
        | TApp { ident; args = [ GType ok; GType err ] }
          when GlobalIdent.equal ident (std_result_mk []) ->
            { monad = Some (MResult err); typ = ok }
        | TApp { ident; args = [ GType ok ] }
          when GlobalIdent.equal ident (std_option_mk []) ->
            { monad = Some MOption; typ = ok }
        | typ -> { monad = None; typ }

      (** the type of pure expression we can return in the monad *)
      let pure_type (x : t) = x.typ

      let lift (e : B.expr) monad_of_e monad_destination : B.expr =
        match (monad_of_e, monad_destination) with
        | m1, m2 when [%equal: B.supported_monads option] m1 m2 -> e
        | None, Some (B.MResult _) ->
            UB.call_Constructor "core" "result" [ "Result"; "Ok" ] [ e ] e.span
              (to_typ { monad = monad_destination; typ = e.typ })
        | None, Some B.MOption ->
            UB.call_Constructor "core" "option" [ "Option"; "Some" ] [ e ]
              e.span
              (to_typ { monad = monad_destination; typ = e.typ })
        | _, Some (B.MException _) ->
            UB.call_Constructor "std" "ops"
              [ "ControlFlow"; "Continue" ]
              [ e ] e.span
              (to_typ { monad = monad_destination; typ = e.typ })
        | m1, m2 ->
            Error.assertion_failure e.span
            @@ "Cannot lift from monad ["
            ^ [%show: B.supported_monads option] m1
            ^ "] to monad ["
            ^ [%show: B.supported_monads option] m2
            ^ "]"

      let lub m1 m2 =
        match (m1, m2) with
        | None, m | m, None -> m
        | (Some (B.MResult _) as m), _ | _, (Some (B.MResult _) as m) -> m
        | _ -> m1

      (** after transformation, are **getting** inside a monad? *)
      let from_typ (old : A.ty) (new_ : B.ty) : t =
        let old = dty (Dummy { id = -1 } (* irrelevant *)) old in
        let monad = from_typ' new_ in
        if B.equal_ty (pure_type monad) old then monad
        else { monad = None; typ = new_ }
    end

    let rec dexpr (expr : A.expr) : B.expr =
      let span = expr.span in
      let typ = dty span expr.typ in
      match expr.e with
      | Let { monadic = Some _; _ } -> .
      | Let { monadic = None; lhs; rhs; body } -> (
          let body' = dexpr body in
          let rhs' = dexpr rhs in
          let mrhs = KnownMonads.from_typ rhs.typ rhs'.typ in
          let lhs = { (dpat lhs) with typ = KnownMonads.pure_type mrhs } in
          match mrhs with
          | { monad = None; _ } ->
              let monadic = None in
              let rhs = rhs' in
              let body = body' in
              { e = Let { monadic; lhs; rhs; body }; span; typ = body.typ }
          | _ ->
              let mbody = KnownMonads.from_typ body.typ body'.typ in
              let m = KnownMonads.lub mbody.monad mrhs.monad in
              let body = KnownMonads.lift body' mbody.monad m in
              let rhs = KnownMonads.lift rhs' mrhs.monad m in
              let monadic =
                match m with
                | None -> None
                | Some m -> Some (m, Features.On.monadic_binding)
              in
              { e = Let { monadic; lhs; rhs; body }; span; typ = body.typ })
      | Match { scrutinee; arms } ->
          let arms =
            List.map
              ~f:(fun { arm = { pat; body = a }; span } ->
                let b = dexpr a in
                let m = KnownMonads.from_typ a.typ b.typ in
                (m, (dpat pat, span, b)))
              arms
          in
          (* Todo throw assertion failed here (to get rid of reduce_exn in favor of reduce) *)
          let m =
            List.map ~f:(fun ({ monad; _ }, _) -> monad) arms
            |> List.reduce ~f:KnownMonads.lub
            |> Option.value_or_thunk ~default:(fun _ ->
                   Error.assertion_failure span "[match] with zero arm?")
          in
          let arms =
            List.map
              ~f:(fun (mself, (pat, span, body)) ->
                let body = KnownMonads.lift body mself.monad m in
                let pat = { pat with typ = body.typ } in
                ({ arm = { pat; body }; span } : B.arm))
              arms
          in
          let scrutinee = dexpr scrutinee in
          {
            e = Match { scrutinee; arms };
            span;
            typ = (List.hd_exn arms).arm.body.typ;
          }
      | If { cond; then_; else_ } ->
          let cond = dexpr cond in
          let then' = dexpr then_ in
          let else' = Option.map ~f:dexpr else_ in
          let mthen = KnownMonads.from_typ then_.typ then'.typ in
          let melse =
            match (else_, else') with
            | Some else_, Some else' -> KnownMonads.from_typ else_.typ else'.typ
            | _ -> mthen
          in
          let m = KnownMonads.lub mthen.monad melse.monad in
          let else_ =
            Option.map
              ~f:(fun else' -> KnownMonads.lift else' melse.monad m)
              else'
          in
          let then_ = KnownMonads.lift then' mthen.monad m in
          { e = If { cond; then_; else_ }; span; typ = then_.typ }
      | Continue _ ->
          Error.unimplemented ~issue_id:96
            ~details:"TODO: Monad for loop-related control flow" span
      | Break _ ->
          Error.unimplemented ~issue_id:96
            ~details:"TODO: Monad for loop-related control flow" span
      | QuestionMark { e; converted_typ; _ } ->
          let e = dexpr e in
          let converted_typ = dty span converted_typ in
          if [%equal: B.ty] converted_typ e.typ then e
          else
            UB.call "std" "ops"
              [ "FromResidual"; "from_residual" ]
              [ e ] span converted_typ
      | Return { e; _ } ->
          let open KnownMonads in
          let e = dexpr e in
          UB.call "std" "ops" [ "ControlFlow"; "Break" ] [ e ] span
            (to_typ @@ { monad = Some (MException e.typ); typ })
      | [%inline_arms
          "dexpr'.*" - Let - Match - If - Continue - Break - QuestionMark
          - Return] ->
          map (fun e -> B.{ e; typ = dty expr.span expr.typ; span = expr.span })

    and lift_if_necessary (e : B.expr) (target_type : B.ty) =
      if B.equal_ty e.typ target_type then e
      else UB.call "dummy" "lift" [] [ e ] e.span target_type

    and dloop_kind = [%inline_body dloop_kind]
    and dloop_state = [%inline_body dloop_state]
    and darm = [%inline_body darm]
    and darm' = [%inline_body darm']
    and dlhs = [%inline_body dlhs]

    module Item = struct
      module OverrideDExpr = struct
        let dexpr (e : A.expr) : B.expr =
          let e' = dexpr e in
          match KnownMonads.from_typ e.typ e'.typ with
          | { monad = Some m; typ } ->
              UB.call "dummy"
                (match m with
                | MException _ -> "mexception"
                | MResult _ -> "mresult"
                | MOption -> "moption")
                [ "run" ] [ e' ] e.span typ
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

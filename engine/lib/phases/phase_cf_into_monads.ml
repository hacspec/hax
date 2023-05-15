open Base
open Utils

module%inlined_contents Make
    (F : Features.T with type monadic_action = Features.Off.monadic_action) =
struct
  open Ast
  module FA = F

  module FB = struct
    include F
    include Features.Off.Continue
    include Features.Off.Early_exit

    (* TODO: when break is introduced: include Features.Off.Break *)
    (* include Features.Off.Mutable_variable *)
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
      (** types of computations *)
      type t =
        | MId of { typ : B.ty }
        | MReturn of { return : B.ty; continue : B.ty }

      let std_ops_control_flow_mk l =
        `Concrete
          { crate = "std"; path = Non_empty_list.("ops" :: "ControlFlow" :: l) }

      let std_ops_control_flow = std_ops_control_flow_mk []

      (** translate a computation type to a simple type *)
      let to_typ : t -> B.ty = function
        | MId { typ } -> typ
        | MReturn { return; continue } ->
            let args = List.map ~f:(fun t -> B.GType t) [ return; continue ] in
            TApp { ident = std_ops_control_flow; args }

      let from_typ' : B.ty -> t = function
        | TApp { ident; args = [ GType return; GType continue ] }
          when GlobalIdent.equal ident std_ops_control_flow ->
            MReturn { return; continue }
        | typ -> MId { typ }

      (** the type of pure expression we can return in the monad *)
      let pure_type = function
        (* *)
        | MId { typ } | MReturn { continue = typ } -> typ

      let lift (e : B.expr) (monad_of_e : t) (monad_destination : t) : B.expr =
        match (monad_of_e, monad_destination) with
        | MId _, MId _ | MReturn _, MReturn _ -> e
        | MId _, MReturn _ ->
            (* TODO: this is a supposed to be Construct node not an App *)
            (* maybe we should just drop Construct in favor of a
               [Record] thing, and put everything which is not a Record
               into an App. This would simplify stuff quite much. Maybe not
               for LHS things. *)
            UB.call "std" "ops"
              [ "ControlFlow"; "Continue" ]
              [ e ] e.span (to_typ monad_destination)
        | _, MId _ ->
            Error.assertion_failure e.span
              "Cannot lift a non-identity monad into the identity monad"

      let lub m1 m2 = match (m1, m2) with MId _, m | m, MId _ -> m | _ -> m1

      (** after transformation, are **getting** inside a monad? *)
      let from_typ (old : A.ty) (new_ : B.ty) : t =
        let old = dty Dummy old in
        let monad = from_typ' new_ in
        if B.equal_ty (pure_type monad) old || true (* TODO: this is broken *)
        then monad
        else MId { typ = new_ }
    end

    let rec dexpr (expr : A.expr) : B.expr =
      let span = expr.span in
      let typ = dty span expr.typ in
      match expr.e with
      | Let { monadic = Some _; lhs; rhs; body } ->
          (* let monadic = monadic || match r with _ -> false in *)
          failwith "todo"
      | Let { monadic = None; lhs; rhs; body } -> (
          let body' = dexpr body in
          let rhs' = dexpr rhs in
          let mrhs = KnownMonads.from_typ rhs.typ rhs'.typ in
          let lhs = { (dpat lhs) with typ = rhs'.typ } in
          match mrhs with
          | MId _ ->
              let monadic = None in
              let rhs = rhs' in
              let body = body' in
              {
                e = Let { monadic = None; lhs; rhs; body };
                span;
                typ = body.typ;
              }
          | _ ->
              let mbody = KnownMonads.from_typ body.typ body'.typ in
              let m = KnownMonads.lub mbody mrhs in
              let body = KnownMonads.lift body' mbody m in
              let rhs = KnownMonads.lift rhs' mrhs m in
              let monadic =
                match m with
                | MId _ -> None
                | _ -> Some Features.On.monadic_binding
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
          (* Todo throw assertion failed here *)
          let m = List.map ~f:fst arms |> List.reduce_exn ~f:KnownMonads.lub in
          let arms =
            List.map
              ~f:(fun (mself, (pat, span, body)) ->
                let body = KnownMonads.lift body mself m in
                let pat = { pat with typ = body.typ } in
                ({ arm = { pat; body }; span } : B.arm))
              arms
          in
          let scrutinee = dexpr scrutinee in
          { e = Match { scrutinee; arms }; span; typ = KnownMonads.to_typ m }
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
          let m = KnownMonads.lub mthen melse in
          let else_ =
            Option.map ~f:(fun else' -> KnownMonads.lift else' melse m) else'
          in
          let then_ = KnownMonads.lift then' mthen m in
          { e = If { cond; then_; else_ }; span; typ = KnownMonads.to_typ m }
      | Continue _ -> failwith "TODO Continue"
      | Break _ -> failwith "TODO Break"
      | Return { e; _ } ->
          let open KnownMonads in
          let e = dexpr e in
          UB.call "std" "ops" [ "ControlFlow"; "Break" ] [ e ] e.span
            (to_typ @@ MReturn { return = (* bad*) e.typ; continue = typ })
      | [%inline_arms "dexpr'.*" - Let - Continue - Break - Return] ->
          map (fun e -> B.{ e; typ = dty expr.span expr.typ; span = expr.span })

    and lift_if_necessary (e : B.expr) (target_type : B.ty) =
      if B.equal_ty e.typ target_type then e
      else UB.call "dummy" "lift" [] [ e ] e.span target_type

    and dloop_kind = [%inline_body dloop_kind]
    and dloop_state = [%inline_body dloop_state]
    and darm = [%inline_body darm]
    and darm' = [%inline_body darm']
    and dlhs = [%inline_body dlhs]

    [%%inline_defs "Item.*"]
  end

  include Implem
end
[@@add "subtype.ml"]

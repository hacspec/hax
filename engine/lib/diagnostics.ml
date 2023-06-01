module T = Raw_thir_ast

module Backend = struct
  type t = Coq | FStar | EasyCrypt
  [@@deriving show { with_path = false }, eq, yojson, compare, hash, sexp]
end

module Phase = struct
  module Rejection = struct
    type t =
      | NotInBackendLang of Backend.t
      | ArbitraryLhs
      | Continue
      | RawOrMutPointer
      | EarlyExit
    [@@deriving show { with_path = false }, eq, yojson, compare, hash, sexp]

    let display = function
      | NotInBackendLang backend -> "not_in_" ^ [%show: Backend.t] backend
      | x -> [%show: t] x
  end

  type t =
    | DirectAndMut
    | Identity
    | DropReferences
    | RefMut
    | ResugarForLoops
    | ResugarQuestionMarks
    | HoistSideEffects
    | LocalMutation
    | TrivializeAssignLhs
    | CfIntoMonads
    | FunctionalizeLoops
    | DummyA
    | DummyB
    | DummyC
    | Reject of Rejection.t
  [@@deriving show { with_path = false }, eq, yojson, compare, hash, sexp]

  let display = function
    | Reject rejection -> "reject_" ^ Rejection.display rejection
    | x -> [%show: t] x
end

module Context = struct
  type t =
    | Phase of Phase.t
    | Backend of Backend.t
    | ThirImport
    | DebugPrintRust
    | Other of string
  [@@deriving show, eq, yojson]
end

type kind = T.kind [@@deriving show, eq]

type t = { context : Context.t; kind : kind; span : T.span }
[@@deriving show, eq]

let to_thir_diagnostic (d : t) : Raw_thir_ast.diagnostics_for__span =
  { kind = d.kind; context = [%show: Context.t] d.context; span = d.span }

let to_thir_loc ({ col; line } : Ast.loc) : T.loc = { col; line }

let to_thir_span (s : Ast.span) : T.span =
  match s with
  | Dummy _ ->
      let hi : T.loc = { col = 0; line = 0 } in
      { filename = Custom "DUNMMY"; hi; lo = hi }
  | Span { file; hi; lo } ->
      {
        filename = Real (LocalPath file);
        hi = to_thir_loc hi;
        lo = to_thir_loc lo;
      }

module Core : sig
  val raise_fatal_error : 'never. t -> 'never
  val report : t -> unit
  val try_ : 'x. (unit -> 'x) -> t list * 'x option
end = struct
  (* a mutable state for collecting errors *)
  let state = ref []
  let report e = state := !state @ [ e ]

  exception Error

  let raise_fatal_error e =
    report e;
    raise Error

  let try_ f =
    let result = try Some (f ()) with Error -> None in
    (!state, result)
end

include Core

let failure ~context ~span kind =
  Core.raise_fatal_error { context; kind; span = to_thir_span span }

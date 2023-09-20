open! Prelude
module T = Types

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
      | AsPattern
    [@@deriving show { with_path = false }, eq, yojson, compare, hash, sexp]

    let display = function
      | NotInBackendLang backend -> "not_in_" ^ [%show: Backend.t] backend
      | x -> [%show: t] x
  end

  type t =
    | DirectAndMut
    | AndMutDefSite
    | Identity
    | DropReferences
    | DropBlocks
    | RefMut
    | ResugarForLoops
    | ResugarForIndexLoops
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

  let display = function
    | Phase p -> Phase.display p
    | Backend backend -> [%show: Backend.t] backend ^ " backend"
    | ThirImport -> "AST import"
    | DebugPrintRust -> "Rust debug printer"
    | Other s -> "Other (" ^ s ^ ")"
end

type kind = T.kind [@@deriving show, eq]

type t = { context : Context.t; kind : kind; span : T.span list }
[@@deriving show, eq]

let to_thir_diagnostic (d : t) : Types.diagnostics_for__array_of__span =
  { kind = d.kind; context = Context.display d.context; span = d.span }

let run_hax_pretty_print_diagnostics (s : string) : string =
  try (Utils.Command.run "hax-pretty-print-diagnostics" s).stdout
  with e ->
    "[run_hax_pretty_print_diagnostics] failed. Exn: " ^ Printexc.to_string e
    ^ ". Here is the JSON representation of the error that occurred:\n" ^ s

let pretty_print : t -> string =
  to_thir_diagnostic >> Types.to_json_diagnostics_for__array_of__span
  >> Yojson.Safe.pretty_to_string >> run_hax_pretty_print_diagnostics

let pretty_print_context_kind : Context.t -> kind -> string =
 fun context kind ->
  let span = Span.to_thir (Span.dummy ()) in
  pretty_print { context; kind; span }

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
  Core.raise_fatal_error { context; kind; span = Span.to_thir span }

module SpanFreeError : sig
  type t = private Data of Context.t * kind

  exception Exn of t

  val payload : t -> Context.t * kind
  val raise : ?span:T.span list -> Context.t -> kind -> 'a
end = struct
  type t = Data of Context.t * kind

  exception Exn of t

  let payload (Data (ctx, kind)) = (ctx, kind)

  let raise_without_reporting (ctx : Context.t) (kind : kind) =
    raise (Exn (Data (ctx, kind)))

  let raise ?(span = []) (ctx : Context.t) (kind : kind) =
    report { span; kind; context = ctx };
    raise_without_reporting ctx kind
end

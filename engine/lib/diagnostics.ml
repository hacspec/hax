module T = Raw_thir_ast

module Backend = struct
  type t = Coq | FStar | EasyCrypt
  [@@deriving show, eq, yojson, compare, hash, sexp]
end

module Phase = struct
  module Rejection = struct
    type t =
      | NotInBackendLang of Backend.t
      | ArbitraryLhs
      | Continue
      | RawOrMutPointer
    [@@deriving show, eq, yojson, compare, hash, sexp]
  end

  type t =
    | DirectAndMut
    | Identity
    | DropReferences
    | RefMut
    | ResugarForLoops
    | MutableVariables
    | Reject of Rejection.t
  [@@deriving show, eq, yojson, compare, hash, sexp]
end

module Context = struct
  type t = Phase of Phase.t | Backend of Backend.t | ThirImport
  [@@deriving show, eq, yojson, compare, hash, sexp]
end

type kind = T.kind [@@deriving show, eq]

type t = {
  context : Context.t;
  kind : kind;
  span : T.span;
  details : string option;
}
[@@deriving show, eq]

exception Error of t

let to_thir_diagnostic (d : t) : Raw_thir_ast.diagnostics_for__span =
  {
    kind = d.kind;
    context = Some ([%show: Context.t * string option] (d.context, d.details));
    span = d.span;
  }

let to_thir_loc ({ col; line } : Ast.loc) : T.loc = { col; line }

let to_thir_span (s : Ast.span) : T.span =
  match s with
  | Dummy ->
      let hi : T.loc = { col = 0; line = 0 } in
      { filename = Custom "DUNMMY"; hi; lo = hi }
  | Span { file; hi; lo } ->
      {
        filename = Real (LocalPath file);
        hi = to_thir_loc hi;
        lo = to_thir_loc lo;
      }

let mk_unimplemented_phase phase (span : Ast.span) (details : string option) =
  raise
    (Error
       {
         span = to_thir_span span;
         kind = T.Unimplemented { details = None };
         context = Phase phase;
         details;
       })

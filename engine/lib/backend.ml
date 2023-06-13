open Base
open Ast

module type BACKEND_OPTIONS = sig
  type t
end

module UnitBackendOptions = struct
  type t = unit
end

module type T = sig
  module InputLanguage : Features.T
  module AST : Ast.T

  module U : sig
    module Mappers : sig
      val rename_global_idents_item :
        (Ast_utils.visit_level -> global_ident -> global_ident) ->
        AST.item ->
        AST.item
    end
  end

  module BackendOptions : BACKEND_OPTIONS

  type analysis_data

  val apply_phases :
    BackendOptions.t -> Ast.Rust.item list -> AST.item list * analysis_data

  val translate :
    BackendOptions.t -> AST.item list -> analysis_data -> Types.file list
end

module type BackendMetadata = sig
  val backend : Diagnostics.Backend.t
end

module Make (InputLanguage : Features.T) (M : BackendMetadata) = struct
  module InputLanguage = InputLanguage
  module AST = Ast.Make (InputLanguage)
  module U = Ast_utils.Make (InputLanguage)
  include M

  module Error = struct
    type t = { kind : Diagnostics.kind; span : Ast.span } [@@deriving show, eq]

    let raise err =
      let context = Diagnostics.Context.Backend M.backend in
      let kind = err.kind in
      let span = Diagnostics.to_thir_span err.span in
      Diagnostics.report { context; kind; span };
      raise @@ Diagnostics.SpanFreeError (context, kind)

    let unimplemented ?issue_id ?details span =
      raise { kind = Unimplemented { issue_id; details }; span }

    let assertion_failure span details =
      raise { kind = AssertionFailure { details }; span }
  end

  let failwith ?(span = Ast.Dummy { id = -1 }) msg =
    Error.unimplemented
      ~details:
        ("[TODO: this error uses failwith, and thus leads to bad error \
          messages, please update it using [Diagnostics.*] helpers] " ^ msg)
      span
    [@@ocaml.deprecated
      "Use more precise errors: Error.unimplemented, Error.assertion_failure \
       or a raw Error.t (with Error.raise)"]
end

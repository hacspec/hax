open! Prelude

module DefaultSubtype = struct
  type error = Err of Span.t [@@deriving show, yojson, eq]

  exception E of error

  let reject (type a b) : Span.t -> a -> b = fun span _ -> raise @@ E (Err span)

  include Features.SUBTYPE.Id

  let explain : error -> Features.Enumeration.t -> string =
   fun _ feat ->
    "a node of kind ["
    ^ [%show: Features.Enumeration.t] feat
    ^ "] have been found in the AST"
end

module Make
    (FA : Features.T)
    (FB : Features.T)
    (S0 : sig
            include Features.SUBTYPE.T

            type error [@@deriving show, yojson, eq]

            exception E of error

            val explain : error -> Features.Enumeration.t -> string
            val metadata : Phase_utils.Metadata.t
          end
          with module A = FA
           and module B = FB) =
struct
  let metadata = S0.metadata

  module S =
    Features.SUBTYPE.Map
      (S0)
      (struct
        let map (type a b) (f : Span.t -> a -> b)
            (feature_kind : Features.Enumeration.t) (span : Span.t) (x : a) : b
            =
          try f span x
          with S0.E err ->
            let span = Span.to_thir span in
            let kind : Diagnostics.kind =
              ExplicitRejection { reason = S0.explain err feature_kind }
            in
            let context : Diagnostics.Context.t =
              Phase S0.metadata.current_phase
            in
            Diagnostics.SpanFreeError.raise ~span context kind
      end)

  include Subtype.Make (FA) (FB) (S)
  module FA = FA
end

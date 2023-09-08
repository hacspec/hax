open! Prelude

module DefaultSubtype = struct
  type error = Err [@@deriving show, yojson, eq]

  exception E of error

  let reject (type a b) : a -> b = fun _ -> raise @@ E Err

  include Features.SUBTYPE.Id

  let explain : error -> Features.Enumeration.t -> string =
   fun _ _ -> "unknown reason"
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
        let map (type a b) (f : a -> b) (feature_kind : Features.Enumeration.t)
            (x : a) : b =
          try f x
          with S0.E err ->
            let kind : Diagnostics.kind =
              ExplicitRejection { reason = S0.explain err feature_kind }
            in
            let context : Diagnostics.Context.t =
              Phase S0.metadata.current_phase
            in
            Diagnostics.SpanFreeError.raise context kind
      end)

  include Subtype.Make (FA) (FB) (S)
  module FA = FA
end

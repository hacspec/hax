open Prelude
include Types

type range = { start : Location.t; end_ : Location.t option }
[@@deriving show, eq, yojson]

module Chunk = struct
  type t = { gen : range; src : range; meta : meta }
  [@@deriving show, eq, yojson]

  let compare (x : t) (y : t) = Location.compare x.gen.start y.gen.start

  let from_spanned ((start, end_, meta) : Spanned.t) : t =
    let gen = { start = start.gen; end_ = end_.gen } in
    let src = { start = start.src; end_ = end_.src } in
    { gen; src; meta }

  let to_spanned ({ gen; src; meta } : t) : Spanned.t =
    ( { gen = gen.start; src = src.start },
      { gen = gen.end_; src = src.end_ },
      meta )

  let%test _ =
    let x = ";AAAA,SAAS,KAAAA,GAAG,YAAAC,GAAU" in
    let s = Instruction.(decode x |> to_points) |> Spanned.from_points in
    [%eq: Spanned.t list] (List.map ~f:(from_spanned >> to_spanned) s) s

  let decode : string -> t list =
    Instruction.(decode >> to_points >> Spanned.from_points)
    >> List.map ~f:from_spanned

  let encode : t list -> string =
    List.map ~f:to_spanned >> Instruction.from_spanned >> Instruction.encode

  let%test _ =
    let x =
      ";AAAA,SAAS,KAAAA,GAAG,YAAAC,GAAU,UAAAC,SAAc;;;ACApC,SAAS,KAAAC,GAAG,aAAAC,SAAiB;AAC7B,SAAS,YAAAC,SAAgB;AAWlB,IAAMC,IAAN,cAA2BF,EAAsC"
    in
    decode x |> encode |> [%eq: string] x
end

include Chunk

open Prelude

let alphabet =
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

let encode (n : int) : char =
  assert (n >= 0 && n < 64);
  String.get alphabet n

let decode (c : char) : int = String.index alphabet c |> Option.value_exn

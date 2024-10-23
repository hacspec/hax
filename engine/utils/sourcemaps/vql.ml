open Prelude

let rec encode_one ?(first = true) (n : int) : int list =
  let n = if first then (Int.abs n lsl 1) + if n < 0 then 1 else 0 else n in
  let lhs, rhs = (n lsr 5, n land 0b11111) in
  let last = Int.equal lhs 0 in
  let output = (if last then 0b000000 else 0b100000) lor rhs in
  output :: (if last then [] else encode_one ~first:false lhs)

let encode : int list -> int list = List.concat_map ~f:encode_one

let encode_base64 : int list -> string =
  encode >> List.map ~f:Base64.encode >> String.of_char_list

let rec decode_one' (first : bool) (l : int list) : int * int list =
  match l with
  | [] -> (0, [])
  | hd :: tl ->
      assert (hd < 64);
      let c = Int.shift_right hd 5 |> Int.bit_and 0b1 in
      let last = Int.equal c 0 in
      if first then
        let sign = match Int.bit_and hd 0b1 with 1 -> -1 | _ -> 1 in
        let hd = Int.shift_right hd 1 |> Int.bit_and 0b1111 in
        if last then (sign * hd, tl)
        else
          let next, tl = decode_one' false tl in
          let value = hd + Int.shift_left next 4 in
          (sign * value, tl)
      else
        let hd = Int.bit_and hd 0b11111 in
        if last then (hd, tl)
        else
          let next, tl = decode_one' false tl in
          (hd + Int.shift_left next 5, tl)

let rec decode (l : int list) : int list =
  match decode_one' true l with n, [] -> [ n ] | n, tl -> n :: decode tl

let decode_base64 : string -> int list =
  String.to_list >> List.map ~f:Base64.decode >> decode

let%test _ =
  let tests =
    [ [ 132; 6; 2323; 64; 32; 63; 31; 65; 33 ]; [ 133123232 ]; [ 0; 0; 0 ] ]
  in
  let tests = tests @ List.map ~f:(List.map ~f:(fun x -> -x)) tests in
  List.for_all ~f:(fun x -> [%eq: int list] x (encode x |> decode)) tests

open Base
open Angstrom

let is_space = function ' ' | '\t' | '\n' -> true | _ -> false

let is_identifier = function
  | '0' .. '9' | 'a' .. 'z' | 'A' .. 'Z' | '_' -> true
  | _ -> false

let is_digit = function '0' .. '9' -> true | _ -> false
let spaces = Fn.const () <$> take_while is_space
let ignore_spaces p = spaces *> p <* spaces
let identifier = ignore_spaces @@ take_while1 is_identifier
let number = ignore_spaces (int_of_string <$> take_while1 is_digit)
let comma = Fn.const () <$> ignore_spaces @@ char ','
let colon = Fn.const () <$> ignore_spaces @@ char ':'
let maybe p = Option.some <$> p <|> return None
let parens p = ignore_spaces (char '(') *> p <* ignore_spaces (char ')')

module type Parser = sig
  type t [@@deriving show, yojson, eq]

  val parser : t Angstrom.t
end

module Make (M : Parser) : sig
  val parse : string -> (M.t, string) Result.t
end = struct
  open M

  let parse = parse_string ~consume:All (parens parser <* end_of_input)
end

module Array = struct
  module M = struct
    type t = {
      array_name : string;
      size : int;
      typ : string;
      index_typ : string option;
    }
    [@@deriving show, yojson, eq]

    let parser =
      let* array_name = identifier <* comma in
      let* size = number <* comma in
      let* typ = identifier in
      let+ index_typ =
        maybe @@ (comma *> string "type_for_indexes" *> colon *> identifier)
      in
      { array_name; size; typ; index_typ }
  end

  include M
  include Make (M)
end

module Bytes = struct
  module M = struct
    type t = { bytes_name : string; size : int } [@@deriving show, yojson, eq]

    let parser =
      let* bytes_name = identifier <* comma in
      let+ size = number in
      { bytes_name; size }
  end

  include M
  include Make (M)
end

let quoted_string = char '"' *> take_while (Char.( <> ) '"') <* char '"'

let quoted_hex =
  char '"'
  *> take_while (function
       | '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' -> true
       | _ -> false)
  <* char '"'

let field name p = string name *> colon *> p
(* let ( <|.> ) p1 p2 = Either.first <$> p1 <|> (Either.second <$> p2) *)

let comment = ignore_spaces (string "//" *> take_while Char.(( <> ) '\n'))
let ignore_comment = Fn.const () <$> maybe comment

module PublicNatMod = struct
  module M = struct
    type t = {
      type_name : string;
      type_of_canvas : string;
      bit_size_of_field : int;
      modulo_value : string;
    }
    [@@deriving show, yojson, eq]

    type t' = {
      type_name : string option;
      type_of_canvas : string option;
      bit_size_of_field : int option;
      modulo_value : string option;
    }

    let parser' : t' Angstrom.t =
      let type_name =
        (fun x acc -> { acc with type_name = Some x })
        <$> field "type_name" identifier
      in
      let type_of_canvas =
        (fun x acc -> { acc with type_of_canvas = Some x })
        <$> field "type_of_canvas" identifier
      in
      let bit_size_of_field =
        (fun x acc -> { acc with bit_size_of_field = Some x })
        <$> field "bit_size_of_field" number
      in
      let modulo_value =
        (fun x acc -> { acc with modulo_value = Some x })
        <$> field "modulo_value" quoted_hex
      in
      let f =
        type_name <|> type_of_canvas <|> bit_size_of_field <|> modulo_value
      in
      let* f1 = f <* comma <* ignore_comment in
      let* f2 = f <* comma <* ignore_comment in
      let* f3 = f <* comma <* ignore_comment in
      let+ f4 = f <* ignore_comment in
      {
        type_name = None;
        type_of_canvas = None;
        bit_size_of_field = None;
        modulo_value = None;
      }
      |> f1 |> f2 |> f3 |> f4

    let parser =
      let* x = parser' in
      match x with
      | {
       type_name = Some type_name;
       type_of_canvas = Some type_of_canvas;
       bit_size_of_field = Some bit_size_of_field;
       modulo_value = Some modulo_value;
      } ->
          return
            ({ type_name; type_of_canvas; bit_size_of_field; modulo_value } : t)
      | _ -> fail "Some fields are missing"
  end

  include M
  include Make (M)
end

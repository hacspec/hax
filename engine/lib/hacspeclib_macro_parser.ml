open Base
open Angstrom
open Utils

let is_space = function ' ' | '\t' | '\n' -> true | _ -> false

let is_identifier = function
  | '0' .. '9' | 'a' .. 'z' | 'A' .. 'Z' | '_' -> true
  | _ -> false

let is_digit = function '0' .. '9' -> true | _ -> false
let spaces = Fn.const () <$> take_while is_space
let ignore_spaces p = spaces *> p <* spaces
let identifier = ignore_spaces @@ take_while1 is_identifier
let number = ignore_spaces (Int.of_string <$> take_while1 is_digit)
let comma = Fn.const () <$> ignore_spaces @@ char ','
let colon = Fn.const () <$> ignore_spaces @@ char ':'
let maybe p = Option.some <$> p <|> return None
let parens p = ignore_spaces (char '(') *> p <* ignore_spaces (char ')')
let square_parens p = ignore_spaces (char '[') *> p <* ignore_spaces (char ']')
let hex_list_identifier = identifier <* comma

let is_hex = function
  | '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' | '_' -> true
  | _ -> false

let is_int_type = function 'u' | 'U' -> true | x -> is_digit x

let remove_underscore (x : string) : string =
  List.fold_left ~init:"" ~f:( ^ ) (split_str ~on:"_" x)

let hex_identifier =
  ignore_spaces
    (string "0x" *> take_while1 is_hex
    >>= (return << ( ^ ) "0x" << remove_underscore))

let hex_list =
  square_parens (many (hex_identifier <* maybe identifier <* maybe comma))

let quoted_string = char '"' *> take_while (Char.( <> ) '"') <* char '"'
let quoted_hex = char '"' *> take_while is_hex <* char '"'
let field name p = string name *> colon *> p
let comment = ignore_spaces (string "//" *> take_while Char.(( <> ) '\n'))
let ignore_comment = Fn.const () <$> maybe comment

let sep_list1 (type a) ~sep (p : a t) : a list t =
  let p = ignore_spaces p in
  let* hd = p in
  let+ tl = many (sep *> p) in
  hd :: tl

let sep_list (type a) ~sep (p : a t) : a list t = option [] (sep_list1 ~sep p)

module RustIntLiteral = struct
  (* *partial* support of https://doc.rust-lang.org/reference/tokens.html#number-literals *)
  let bin_digit = satisfy [%matches? '0' | '1']

  let oct_digit =
    satisfy [%matches? '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7']

  let dec_digit = satisfy is_digit
  let hex_digit = satisfy is_hex

  let mk (prefix : string t) (o : char t) : string t =
    let underscore : char option t = Fn.const None <$> char '_' in
    let* prefix = prefix in
    let* hd = o in
    let+ tl = many (Option.some <$> o <|> underscore) in
    prefix ^ String.of_char_list @@ List.filter_map ~f:Fn.id (Some hd :: tl)

  let dec_literal = mk (string "") dec_digit
  let bin_literal = mk (string "0b") bin_digit
  let oct_literal = mk (string "0o") oct_digit
  let hex_literal = mk (string "0x") hex_digit

  let signedness =
    let open Ast in
    Fn.const Unsigned <$> char 'u' <|> (Fn.const Signed <$> char 'i')

  let size =
    let open Ast in
    let h size str = Fn.const size <$> string str in
    choice [ h S8 "8"; h S16 "16"; h S32 "32"; h S64 "64"; h S128 "128" ]

  let suffix : Ast.int_kind t =
    let open Ast in
    let* signedness = signedness in
    let+ size = size in
    { size; signedness }

  let integer_literal =
    let* value = bin_literal <|> oct_literal <|> hex_literal <|> dec_literal in
    let+ kind = suffix in
    (value, kind)
end

let rust_int_type = RustIntLiteral.suffix

let array_of_int_literal =
  ignore_spaces (char '[') *> sep_list ~sep:comma RustIntLiteral.integer_literal
  <* ignore_spaces (char ']')

module type Parser = sig
  type t [@@deriving show, yojson, eq]

  val name : string
  val parser : t Angstrom.t
end

module Make (M : Parser) : sig
  val parse : string -> (M.t, string) Result.t
end = struct
  open M

  let parse input =
    match parse_string ~consume:All (parens parser <* end_of_input) input with
    | Ok e -> Ok e
    | Error e ->
        Out_channel.output_string Out_channel.stderr
        @@ "########## Error while parsing: (" ^ name ^ ")";
        Out_channel.output_string Out_channel.stderr input;
        Out_channel.output_string Out_channel.stderr e;
        Error e
end

module Array = struct
  module M = struct
    type t = {
      array_name : string;
      size : string;
      typ : string;
      index_typ : string option;
    }
    [@@deriving show, yojson, eq]

    let parser =
      let* array_name = identifier <* comma in
      let* size = identifier <* comma in
      let* typ = identifier in
      let+ index_typ =
        maybe @@ (comma *> string "type_for_indexes" *> colon *> identifier)
      in
      { array_name; size; typ; index_typ }

    let name = "array"
  end

  include M
  include Make (M)
end

module Bytes = struct
  module M = struct
    type t = { bytes_name : string; size : string }
    [@@deriving show, yojson, eq]

    let parser =
      let* bytes_name = identifier <* comma in
      let+ size = identifier in
      { bytes_name; size }

    let name = "bytes"
  end

  include M
  include Make (M)
end

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
      let* f1 = ignore_comment *> f <* comma <* ignore_comment in
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

    let name = "public_nat_mod"
  end

  include M
  include Make (M)
end

module SecretBytes = struct
  module M = struct
    type t = (string * Ast.int_kind) list [@@deriving show, yojson, eq]

    let parser = array_of_int_literal
    let name = "secret_bytes"
  end

  include M
  include Make (M)
end

module SecretArray = struct
  module M = struct
    type t = {
      int_typ_size : Ast.size;
      array_values : (string * Ast.int_kind) list;
    }
    [@@deriving show, yojson, eq]

    let parser =
      let hacspec_int_type =
        let* _ = string "U" in
        (* only unsigned *)
        RustIntLiteral.size
        (* let ident = *)
        (*   `Concrete Ast.{ crate = "dummy"; path = Non_empty_list.[ c ^ size ] } *)
        (* in *)
        (* AST.TApp { ident; args = [] } *)
      in
      let* int_typ_size = hacspec_int_type in
      let* _ = comma in
      let* array_values = array_of_int_literal in
      let+ _ = option () comma in
      { int_typ_size; array_values }

    let name = "secret_array"
  end

  include M
  include Make (M)
end

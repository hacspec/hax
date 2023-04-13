module UChar = BatUChar
module U32 = FStar_UInt32
type char = int
val char_to_yojson : char -> Yojson.Safe.t
val char_of_yojson :
  Yojson.Safe.t -> char Ppx_deriving_yojson_runtime.error_or
val _ : Yojson.Safe.t -> char Ppx_deriving_yojson_runtime.error_or
val pp_char :
  Ppx_deriving_runtime.Format.formatter -> char -> Ppx_deriving_runtime.unit
val show_char : char -> Ppx_deriving_runtime.string
type char_code = U32.t
val lowercase : char -> char
val uppercase : char -> char
val int_of_char : char -> Z.t
val char_of_int : Z.t -> char
val u32_of_char : char -> char_code
val char_of_u32 : char_code -> char

type char = FStar_Char.char
val char_to_yojson : char -> Yojson.Safe.t
val char_of_yojson :
  Yojson.Safe.t -> char Ppx_deriving_yojson_runtime.error_or
val pp_char :
  Ppx_deriving_runtime.Format.formatter -> char -> Ppx_deriving_runtime.unit
val show_char : char -> Ppx_deriving_runtime.string
type float = FStar_Float.float
val float_to_yojson : float -> Yojson.Safe.t
val float_of_yojson :
  Yojson.Safe.t -> float Ppx_deriving_yojson_runtime.error_or
val pp_float :
  Ppx_deriving_runtime.Format.formatter -> float -> Ppx_deriving_runtime.unit
val show_float : float -> Ppx_deriving_runtime.string
type double = FStar_Float.double
val double_to_yojson : double -> Yojson.Safe.t
val double_of_yojson :
  Yojson.Safe.t -> double Ppx_deriving_yojson_runtime.error_or
val pp_double :
  Ppx_deriving_runtime.Format.formatter ->
  double -> Ppx_deriving_runtime.unit
val show_double : double -> Ppx_deriving_runtime.string
type byte = FStar_UInt8.byte
val byte_to_yojson : byte -> Yojson.Safe.t
val byte_of_yojson :
  Yojson.Safe.t -> byte Ppx_deriving_yojson_runtime.error_or
val _ : Yojson.Safe.t -> byte Ppx_deriving_yojson_runtime.error_or
val pp_byte :
  Ppx_deriving_runtime.Format.formatter -> byte -> Ppx_deriving_runtime.unit
val show_byte : byte -> Ppx_deriving_runtime.string
type int8 = FStar_Int8.int8
type uint8 = FStar_UInt8.uint8
type int16 = FStar_Int16.int16
type uint16 = FStar_UInt16.uint16
type int32 = FStar_Int32.int32
type int64 = FStar_Int64.int64

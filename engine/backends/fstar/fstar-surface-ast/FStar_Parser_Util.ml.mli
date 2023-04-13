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
type single = float
type decimal = int
type bytes = byte array
val parseState : unit
val pos_of_lexpos : Lexing.position -> FStar_Compiler_Range.pos
val mksyn_range :
  Lexing.position -> Lexing.position -> FStar_Compiler_Range.range
val getLexerRange : Lexing.lexbuf -> FStar_Compiler_Range.range
val lhs : unit -> FStar_Compiler_Range.range
val rhs : unit -> int -> FStar_Compiler_Range.range
val rhspos : unit -> int -> FStar_Compiler_Range.pos
val rhs2 : unit -> int -> int -> FStar_Compiler_Range.range
exception WrappedError of exn * FStar_Compiler_Range.range
exception ReportedError
exception StopProcessing
val warningHandler : (exn -> unit) ref
val errorHandler : (exn -> unit) ref
val errorAndWarningCount : int ref
val errorR : exn -> unit
val warning : exn -> unit
val comments : (string * FStar_Compiler_Range.range) list ref
val add_comment : string * FStar_Compiler_Range.range -> unit
val flush_comments : unit -> (string * FStar_Compiler_Range.range) list

type uint8 = int
val uint8_to_yojson : uint8 -> Yojson.Safe.t
val uint8_of_yojson :
  Yojson.Safe.t -> uint8 Ppx_deriving_yojson_runtime.error_or
val pp_uint8 :
  Ppx_deriving_runtime.Format.formatter -> uint8 -> Ppx_deriving_runtime.unit
val show_uint8 : uint8 -> Ppx_deriving_runtime.string
type byte = uint8
val byte_to_yojson : byte -> Yojson.Safe.t
val byte_of_yojson :
  Yojson.Safe.t -> byte Ppx_deriving_yojson_runtime.error_or
val pp_byte :
  Ppx_deriving_runtime.Format.formatter -> byte -> Ppx_deriving_runtime.unit
val show_byte : byte -> Ppx_deriving_runtime.string
type t = uint8
val to_yojson : t -> Yojson.Safe.t
val of_yojson : Yojson.Safe.t -> t Ppx_deriving_yojson_runtime.error_or
val pp :
  Ppx_deriving_runtime.Format.formatter -> t -> Ppx_deriving_runtime.unit
val show : t -> Ppx_deriving_runtime.string
type t' = t
val t'_to_yojson : t' -> Yojson.Safe.t
val t'_of_yojson : Yojson.Safe.t -> t' Ppx_deriving_yojson_runtime.error_or
val _ : Yojson.Safe.t -> t' Ppx_deriving_yojson_runtime.error_or
val pp_t' :
  Ppx_deriving_runtime.Format.formatter -> t' -> Ppx_deriving_runtime.unit
val show_t' : t' -> Ppx_deriving_runtime.string
val ( % ) : int -> int -> int
val n : Z.t
val v : uint8 -> Prims.int
val zero : int
val one : int
val ones : int
val add : uint8 -> uint8 -> uint8
val add_underspec : uint8 -> uint8 -> int
val add_mod : uint8 -> uint8 -> int
val sub : uint8 -> uint8 -> uint8
val sub_underspec : uint8 -> uint8 -> int
val sub_mod : uint8 -> uint8 -> int
val mul : uint8 -> uint8 -> uint8
val mul_underspec : uint8 -> uint8 -> int
val mul_mod : uint8 -> uint8 -> int
val div : uint8 -> uint8 -> uint8
val rem : uint8 -> uint8 -> uint8
val logand : uint8 -> uint8 -> uint8
val logxor : uint8 -> uint8 -> uint8
val logor : uint8 -> uint8 -> uint8
val lognot : uint8 -> uint8
val int_to_uint8 : Prims.int -> uint8
val shift_right : uint8 -> Stdint.Uint32.t -> uint8
val shift_left : uint8 -> Stdint.Uint32.t -> uint8
val eq : uint8 -> uint8 -> bool
val gt : uint8 -> uint8 -> bool
val gte : uint8 -> uint8 -> bool
val lt : uint8 -> uint8 -> bool
val lte : uint8 -> uint8 -> bool
val gte_mask : uint8 -> uint8 -> uint8
val eq_mask : uint8 -> uint8 -> uint8
val op_Plus_Hat : uint8 -> uint8 -> uint8
val op_Plus_Question_Hat : uint8 -> uint8 -> int
val op_Plus_Percent_Hat : uint8 -> uint8 -> int
val op_Subtraction_Hat : uint8 -> uint8 -> uint8
val op_Subtraction_Question_Hat : uint8 -> uint8 -> int
val op_Subtraction_Percent_Hat : uint8 -> uint8 -> int
val op_Star_Hat : uint8 -> uint8 -> uint8
val op_Star_Question_Hat : uint8 -> uint8 -> int
val op_Star_Percent_Hat : uint8 -> uint8 -> int
val op_Slash_Hat : uint8 -> uint8 -> uint8
val op_Percent_Hat : uint8 -> uint8 -> uint8
val op_Hat_Hat : uint8 -> uint8 -> uint8
val op_Amp_Hat : uint8 -> uint8 -> uint8
val op_Bar_Hat : uint8 -> uint8 -> uint8
val op_Less_Less_Hat : uint8 -> Stdint.Uint32.t -> uint8
val op_Greater_Greater_Hat : uint8 -> Stdint.Uint32.t -> uint8
val op_Equals_Hat : uint8 -> uint8 -> bool
val op_Greater_Hat : uint8 -> uint8 -> bool
val op_Greater_Equals_Hat : uint8 -> uint8 -> bool
val op_Less_Hat : uint8 -> uint8 -> bool
val op_Less_Equals_Hat : uint8 -> uint8 -> bool
val of_string : string -> int
val to_string : int -> string
val to_string_hex : int -> string
val to_string_hex_pad : int -> string
val uint_to_t : Prims.int -> uint8
val to_int : 'a -> 'a
val __uint_to_t : Prims.int -> uint8

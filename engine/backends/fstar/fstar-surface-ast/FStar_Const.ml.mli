type signedness = Unsigned | Signed
val signedness_to_yojson : signedness -> Yojson.Safe.t
val signedness_of_yojson :
  Yojson.Safe.t -> signedness Ppx_deriving_yojson_runtime.error_or
val pp_signedness :
  Ppx_deriving_runtime.Format.formatter ->
  signedness -> Ppx_deriving_runtime.unit
val show_signedness : signedness -> Ppx_deriving_runtime.string
val uu___is_Unsigned : signedness -> Prims.bool
val uu___is_Signed : signedness -> Prims.bool
type width = Int8 | Int16 | Int32 | Int64 | Sizet
val width_to_yojson : width -> Yojson.Safe.t
val width_of_yojson :
  Yojson.Safe.t -> width Ppx_deriving_yojson_runtime.error_or
val pp_width :
  Ppx_deriving_runtime.Format.formatter -> width -> Ppx_deriving_runtime.unit
val show_width : width -> Ppx_deriving_runtime.string
val uu___is_Int8 : width -> Prims.bool
val uu___is_Int16 : width -> Prims.bool
val uu___is_Int32 : width -> Prims.bool
val uu___is_Int64 : width -> Prims.bool
val uu___is_Sizet : width -> Prims.bool
type sconst =
    Const_effect
  | Const_unit
  | Const_bool of Prims.bool
  | Const_int of
      (Prims.string * (signedness * width) FStar_Pervasives_Native.option)
  | Const_char of FStar_BaseTypes.char
  | Const_real of Prims.string
  | Const_string of (Prims.string * FStar_Compiler_Range.range)
  | Const_range_of
  | Const_set_range_of
  | Const_range of FStar_Compiler_Range.range
  | Const_reify of FStar_Ident.lid FStar_Pervasives_Native.option
  | Const_reflect of FStar_Ident.lid
val sconst_to_yojson : sconst -> Yojson.Safe.t
val sconst_of_yojson :
  Yojson.Safe.t -> sconst Ppx_deriving_yojson_runtime.error_or
val _ : Yojson.Safe.t -> sconst Ppx_deriving_yojson_runtime.error_or
val pp_sconst :
  Ppx_deriving_runtime.Format.formatter ->
  sconst -> Ppx_deriving_runtime.unit
val show_sconst : sconst -> Ppx_deriving_runtime.string
val uu___is_Const_effect : sconst -> Prims.bool
val uu___is_Const_unit : sconst -> Prims.bool
val uu___is_Const_bool : sconst -> Prims.bool
val __proj__Const_bool__item___0 : sconst -> Prims.bool
val uu___is_Const_int : sconst -> Prims.bool
val __proj__Const_int__item___0 :
  sconst ->
  Prims.string * (signedness * width) FStar_Pervasives_Native.option
val uu___is_Const_char : sconst -> Prims.bool
val __proj__Const_char__item___0 : sconst -> FStar_BaseTypes.char
val uu___is_Const_real : sconst -> Prims.bool
val __proj__Const_real__item___0 : sconst -> Prims.string
val uu___is_Const_string : sconst -> Prims.bool
val __proj__Const_string__item___0 :
  sconst -> Prims.string * FStar_Compiler_Range.range
val uu___is_Const_range_of : sconst -> Prims.bool
val uu___is_Const_set_range_of : sconst -> Prims.bool
val uu___is_Const_range : sconst -> Prims.bool
val __proj__Const_range__item___0 : sconst -> FStar_Compiler_Range.range
val uu___is_Const_reify : sconst -> Prims.bool
val __proj__Const_reify__item___0 :
  sconst -> FStar_Ident.lid FStar_Pervasives_Native.option
val uu___is_Const_reflect : sconst -> Prims.bool
val __proj__Const_reflect__item___0 : sconst -> FStar_Ident.lid
val eq_const : sconst -> sconst -> Prims.bool
val pow2 : FStar_BigInt.bigint -> FStar_BigInt.bigint
val bounds : signedness -> width -> FStar_BigInt.bigint * FStar_BigInt.bigint
val within_bounds : Prims.string -> signedness -> width -> Prims.bool

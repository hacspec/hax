type ident = { idText : Prims.string; idRange : FStar_Compiler_Range.range; }
val ident_to_yojson : ident -> Yojson.Safe.t
val ident_of_yojson :
  Yojson.Safe.t -> ident Ppx_deriving_yojson_runtime.error_or
val pp_ident :
  Ppx_deriving_runtime.Format.formatter -> ident -> Ppx_deriving_runtime.unit
val show_ident : ident -> Ppx_deriving_runtime.string
val __proj__Mkident__item__idText : ident -> Prims.string
val __proj__Mkident__item__idRange : ident -> FStar_Compiler_Range.range
type path = Prims.string Prims.list
val path_to_yojson : path -> Yojson.Safe.t
val path_of_yojson :
  Yojson.Safe.t -> path Ppx_deriving_yojson_runtime.error_or
val pp_path :
  Ppx_deriving_runtime.Format.formatter -> path -> Ppx_deriving_runtime.unit
val show_path : path -> Ppx_deriving_runtime.string
type ipath = ident Prims.list
val ipath_to_yojson : ipath -> Yojson.Safe.t
val ipath_of_yojson :
  Yojson.Safe.t -> ipath Ppx_deriving_yojson_runtime.error_or
val pp_ipath :
  Ppx_deriving_runtime.Format.formatter -> ipath -> Ppx_deriving_runtime.unit
val show_ipath : ipath -> Ppx_deriving_runtime.string
type lident = {
  ns : ipath;
  ident : ident;
  nsstr : Prims.string;
  str : Prims.string;
}
val lident_to_yojson : lident -> Yojson.Safe.t
val lident_of_yojson :
  Yojson.Safe.t -> lident Ppx_deriving_yojson_runtime.error_or
val pp_lident :
  Ppx_deriving_runtime.Format.formatter ->
  lident -> Ppx_deriving_runtime.unit
val show_lident : lident -> Ppx_deriving_runtime.string
val __proj__Mklident__item__ns : lident -> ipath
val __proj__Mklident__item__ident : lident -> ident
val __proj__Mklident__item__nsstr : lident -> Prims.string
val __proj__Mklident__item__str : lident -> Prims.string
val mk_ident : Prims.string * FStar_Compiler_Range.range -> ident
val set_id_range : FStar_Compiler_Range.range -> ident -> ident
val reserved_prefix : Prims.string
val uu___32 :
  ((Prims.unit -> Prims.int) * (Prims.unit -> Prims.unit)) *
  Prims.int FStar_Compiler_Effect.ref
val _gen : (Prims.unit -> Prims.int) * (Prims.unit -> Prims.unit)
val _secret_ref : Prims.int FStar_Compiler_Effect.ref
val next_id : Prims.unit -> Prims.int
val reset_gensym : Prims.unit -> Prims.unit
val with_frozen_gensym : (Prims.unit -> 'a) -> 'a
val gen' : Prims.string -> FStar_Compiler_Range.range -> ident
val gen : FStar_Compiler_Range.range -> ident
val ident_of_lid : lident -> ident
val range_of_id : ident -> FStar_Compiler_Range.range
val id_of_text : Prims.string -> ident
val string_of_id : ident -> Prims.string
val text_of_path : path -> Prims.string
val path_of_text : Prims.string -> path
val path_of_ns : ipath -> path
val path_of_lid : lident -> path
val ns_of_lid : lident -> ipath
val ids_of_lid : lident -> ipath
val lid_of_ns_and_id : ipath -> ident -> lident
val lid_of_ids : ipath -> lident
val lid_of_str : Prims.string -> lident
val lid_of_path : path -> FStar_Compiler_Range.range -> lident
val text_of_lid : lident -> Prims.string
val lid_equals : lident -> lident -> Prims.bool
val ident_equals : ident -> ident -> Prims.bool
type lid = lident
val lid_to_yojson : lid -> Yojson.Safe.t
val lid_of_yojson : Yojson.Safe.t -> lid Ppx_deriving_yojson_runtime.error_or
val _ : Yojson.Safe.t -> lid Ppx_deriving_yojson_runtime.error_or
val pp_lid :
  Ppx_deriving_runtime.Format.formatter -> lid -> Ppx_deriving_runtime.unit
val show_lid : lid -> Ppx_deriving_runtime.string
val range_of_lid : lident -> FStar_Compiler_Range.range
val set_lid_range : lident -> FStar_Compiler_Range.range -> lident
val lid_add_suffix : lident -> Prims.string -> lident
val ml_path_of_lid : lident -> Prims.string
val string_of_lid : lident -> Prims.string
val qual_id : lident -> ident -> lident
val nsstr : lident -> Prims.string

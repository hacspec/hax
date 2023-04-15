type file_name = Prims.string
val file_name_to_yojson : file_name -> Yojson.Safe.t
val file_name_of_yojson :
  Yojson.Safe.t -> file_name Ppx_deriving_yojson_runtime.error_or
val pp_file_name :
  Ppx_deriving_runtime.Format.formatter ->
  file_name -> Ppx_deriving_runtime.unit
val show_file_name : file_name -> Ppx_deriving_runtime.string
type pos = { line : Prims.int; col : Prims.int; }
val pos_to_yojson : pos -> Yojson.Safe.t
val pos_of_yojson : Yojson.Safe.t -> pos Ppx_deriving_yojson_runtime.error_or
val pp_pos :
  Ppx_deriving_runtime.Format.formatter -> pos -> Ppx_deriving_runtime.unit
val show_pos : pos -> Ppx_deriving_runtime.string
val __proj__Mkpos__item__line : pos -> Prims.int
val __proj__Mkpos__item__col : pos -> Prims.int
val max : Prims.int -> Prims.int -> Prims.int
val pos_geq : pos -> pos -> Prims.bool
type rng = { file_name : file_name; start_pos : pos; end_pos : pos; }
val rng_to_yojson : rng -> Yojson.Safe.t
val rng_of_yojson : Yojson.Safe.t -> rng Ppx_deriving_yojson_runtime.error_or
val pp_rng :
  Ppx_deriving_runtime.Format.formatter -> rng -> Ppx_deriving_runtime.unit
val show_rng : rng -> Ppx_deriving_runtime.string
val __proj__Mkrng__item__file_name : rng -> file_name
val __proj__Mkrng__item__start_pos : rng -> pos
val __proj__Mkrng__item__end_pos : rng -> pos
type range = { def_range : rng; use_range : rng; }
val range_to_yojson : range -> Yojson.Safe.t
val range_of_yojson :
  Yojson.Safe.t -> range Ppx_deriving_yojson_runtime.error_or
val _ : Yojson.Safe.t -> range Ppx_deriving_yojson_runtime.error_or
val pp_range :
  Ppx_deriving_runtime.Format.formatter -> range -> Ppx_deriving_runtime.unit
val show_range : range -> Ppx_deriving_runtime.string
val __proj__Mkrange__item__def_range : range -> rng
val __proj__Mkrange__item__use_range : range -> rng
val dummy_pos : pos
val dummy_rng : rng
val dummyRange : range
val use_range : range -> rng
val def_range : range -> rng
val range_of_rng : rng -> rng -> range
val set_use_range : range -> rng -> range
val set_def_range : range -> rng -> range
val mk_pos : Prims.int -> Prims.int -> pos
val mk_rng : file_name -> pos -> pos -> rng
val mk_range : Prims.string -> pos -> pos -> range
val union_rng : rng -> rng -> rng
val union_ranges : range -> range -> range
val rng_included : rng -> rng -> Prims.bool
val string_of_pos : pos -> Prims.string
val string_of_file_name : Prims.string -> Prims.string
val file_of_range : range -> Prims.string
val set_file_of_range : range -> Prims.string -> range
val string_of_rng : rng -> Prims.string
val string_of_def_range : range -> Prims.string
val string_of_use_range : range -> Prims.string
val string_of_range : range -> Prims.string
val start_of_range : range -> pos
val end_of_range : range -> pos
val file_of_use_range : range -> Prims.string
val start_of_use_range : range -> pos
val end_of_use_range : range -> pos
val line_of_pos : pos -> Prims.int
val col_of_pos : pos -> Prims.int
val end_range : range -> range
val compare_rng : rng -> rng -> Prims.int
val compare : range -> range -> Prims.int
val compare_use_range : range -> range -> Prims.int
val range_before_pos : range -> pos -> Prims.bool
val end_of_line : pos -> pos
val extend_to_end_of_line : range -> range
val prims_to_fstar_range :
  (Prims.string * (Prims.int * Prims.int) * (Prims.int * Prims.int)) *
  (Prims.string * (Prims.int * Prims.int) * (Prims.int * Prims.int)) -> 
  range
val json_of_pos : pos -> FStar_Compiler_Util.json
val json_of_range_fields :
  Prims.string -> pos -> pos -> FStar_Compiler_Util.json
val json_of_use_range : range -> FStar_Compiler_Util.json
val json_of_def_range : range -> FStar_Compiler_Util.json

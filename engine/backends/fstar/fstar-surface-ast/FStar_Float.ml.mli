type double = float
val double_to_yojson : double -> Yojson.Safe.t
val double_of_yojson :
  Yojson.Safe.t -> double Ppx_deriving_yojson_runtime.error_or
val pp_double :
  Ppx_deriving_runtime.Format.formatter ->
  double -> Ppx_deriving_runtime.unit
val show_double : double -> Ppx_deriving_runtime.string
type float = double
val float_to_yojson : float -> Yojson.Safe.t
val float_of_yojson :
  Yojson.Safe.t -> float Ppx_deriving_yojson_runtime.error_or
val _ : Yojson.Safe.t -> float Ppx_deriving_yojson_runtime.error_or
val pp_float :
  Ppx_deriving_runtime.Format.formatter -> float -> Ppx_deriving_runtime.unit
val show_float : float -> Ppx_deriving_runtime.string

val op_Bar_Greater : 'a -> ('a -> 'b) -> 'b
val op_Less_Bar : ('a -> 'b) -> 'a -> 'b
type 'a ref' = 'a ref
val ref'_to_yojson : ('a -> Yojson.Safe.t) -> 'a ref' -> Yojson.Safe.t
val ref'_of_yojson :
  (Yojson.Safe.t -> 'a Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t -> 'a ref' Ppx_deriving_yojson_runtime.error_or
val pp_ref' :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  Ppx_deriving_runtime.Format.formatter ->
  'a ref' -> Ppx_deriving_runtime.unit
val show_ref' :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  'a ref' -> Ppx_deriving_runtime.string
type 'a ref = 'a ref'
val ref_to_yojson : ('a -> Yojson.Safe.t) -> 'a ref -> Yojson.Safe.t
val ref_of_yojson :
  (Yojson.Safe.t -> 'a Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t -> 'a ref Ppx_deriving_yojson_runtime.error_or
val _ :
  (Yojson.Safe.t -> 'a Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t -> 'a ref Ppx_deriving_yojson_runtime.error_or
val pp_ref :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  Ppx_deriving_runtime.Format.formatter ->
  'a ref -> Ppx_deriving_runtime.unit
val show_ref :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  'a ref -> Ppx_deriving_runtime.string
val op_Bang : 'a ref -> 'a
val op_Colon_Equals : 'a Stdlib.ref -> 'a -> unit
val alloc : 'a -> 'a Stdlib.ref
val raise : exn -> 'a
val exit : Z.t -> 'a
val try_with : (unit -> 'a) -> (exn -> 'a) -> 'a
exception Failure of string
val failwith : string -> 'a

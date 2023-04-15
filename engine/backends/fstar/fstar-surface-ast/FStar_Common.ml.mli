val has_cygpath : Prims.bool
val try_convert_file_name_to_mixed : Prims.string -> Prims.string
val snapshot :
  ('a -> 'b) ->
  'c Prims.list FStar_Compiler_Effect.ref -> 'a -> Prims.int * 'b
val rollback :
  (Prims.unit -> 'a) ->
  'c Prims.list FStar_Compiler_Effect.ref ->
  Prims.int FStar_Pervasives_Native.option -> 'a
val raise_failed_assertion : Prims.string -> 'uuuuu
val runtime_assert : Prims.bool -> Prims.string -> Prims.unit
val __string_of_list :
  Prims.string -> ('a -> Prims.string) -> 'a Prims.list -> Prims.string
val string_of_list :
  Prims.unit -> ('uuuuu -> Prims.string) -> 'uuuuu Prims.list -> Prims.string
val string_of_list' :
  Prims.unit -> ('uuuuu -> Prims.string) -> 'uuuuu Prims.list -> Prims.string
val string_of_set :
  ('a -> Prims.string) -> 'a FStar_Compiler_Util.set -> Prims.string
val list_of_option : 'a FStar_Pervasives_Native.option -> 'a Prims.list
val string_of_option :
  ('uuuuu -> Prims.string) ->
  'uuuuu FStar_Pervasives_Native.option -> Prims.string
val tabulate : Prims.int -> (Prims.int -> 'a) -> 'a Prims.list
val max_prefix :
  ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list * 'a Prims.list
val max_suffix :
  ('a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list * 'a Prims.list

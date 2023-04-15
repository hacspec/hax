val isNone : 'a FStar_Pervasives_Native.option -> Prims.bool
val isSome : 'a FStar_Pervasives_Native.option -> Prims.bool
val map :
  ('a -> 'b) ->
  'a FStar_Pervasives_Native.option -> 'b FStar_Pervasives_Native.option
val mapTot :
  ('a -> 'b) ->
  'a FStar_Pervasives_Native.option -> 'b FStar_Pervasives_Native.option
val get : 'a FStar_Pervasives_Native.option -> 'a

type 'a option' = 'a option = None | Some of 'a
val option'_to_yojson : ('a -> Yojson.Safe.t) -> 'a option' -> Yojson.Safe.t
val option'_of_yojson :
  (Yojson.Safe.t -> 'a Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t -> 'a option' Ppx_deriving_yojson_runtime.error_or
val pp_option' :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  Ppx_deriving_runtime.Format.formatter ->
  'a option' -> Ppx_deriving_runtime.unit
val show_option' :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  'a option' -> Ppx_deriving_runtime.string
type 'a option = 'a option' = None | Some of 'a
val option_to_yojson : ('a -> Yojson.Safe.t) -> 'a option -> Yojson.Safe.t
val option_of_yojson :
  (Yojson.Safe.t -> 'a Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t -> 'a option Ppx_deriving_yojson_runtime.error_or
val pp_option :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  Ppx_deriving_runtime.Format.formatter ->
  'a option -> Ppx_deriving_runtime.unit
val show_option :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  'a option -> Ppx_deriving_runtime.string
val uu___is_None : 'a option -> bool
val uu___is_Some : 'a option -> bool
val __proj__Some__item__v : 'a option -> 'a
type ('a, 'b) tuple2 = 'a * 'b
val tuple2_to_yojson :
  ('a -> Yojson.Safe.t) ->
  ('b -> Yojson.Safe.t) -> ('a, 'b) tuple2 -> Yojson.Safe.t
val tuple2_of_yojson :
  (Yojson.Safe.t -> 'a Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'b Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t -> ('a, 'b) tuple2 Ppx_deriving_yojson_runtime.error_or
val pp_tuple2 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  Ppx_deriving_runtime.Format.formatter ->
  ('a, 'b) tuple2 -> Ppx_deriving_runtime.unit
val show_tuple2 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  ('a, 'b) tuple2 -> Ppx_deriving_runtime.string
val fst : 'a * 'b -> 'a
val snd : 'a * 'b -> 'b
val __proj__Mktuple2__1 : 'a * 'b -> 'a
val __proj__Mktuple2__2 : 'a * 'b -> 'b
type ('a, 'b, 'c) tuple3 = 'a * 'b * 'c
val tuple3_to_yojson :
  ('a -> Yojson.Safe.t) ->
  ('b -> Yojson.Safe.t) ->
  ('c -> Yojson.Safe.t) -> ('a, 'b, 'c) tuple3 -> Yojson.Safe.t
val tuple3_of_yojson :
  (Yojson.Safe.t -> 'a Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'b Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'c Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t -> ('a, 'b, 'c) tuple3 Ppx_deriving_yojson_runtime.error_or
val pp_tuple3 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'c -> Ppx_deriving_runtime.unit) ->
  Ppx_deriving_runtime.Format.formatter ->
  ('a, 'b, 'c) tuple3 -> Ppx_deriving_runtime.unit
val show_tuple3 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'c -> Ppx_deriving_runtime.unit) ->
  ('a, 'b, 'c) tuple3 -> Ppx_deriving_runtime.string
val uu___is_Mktuple3 : 'a -> bool
val __proj__Mktuple3__item___1 : 'a * 'b * 'c -> 'a
val __proj__Mktuple3__item___2 : 'a * 'b * 'c -> 'b
val __proj__Mktuple3__item___3 : 'a * 'b * 'c -> 'c
type ('a, 'b, 'c, 'd) tuple4 = 'a * 'b * 'c * 'd
val tuple4_to_yojson :
  ('a -> Yojson.Safe.t) ->
  ('b -> Yojson.Safe.t) ->
  ('c -> Yojson.Safe.t) ->
  ('d -> Yojson.Safe.t) -> ('a, 'b, 'c, 'd) tuple4 -> Yojson.Safe.t
val tuple4_of_yojson :
  (Yojson.Safe.t -> 'a Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'b Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'c Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'd Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t ->
  ('a, 'b, 'c, 'd) tuple4 Ppx_deriving_yojson_runtime.error_or
val pp_tuple4 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'c -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'd -> Ppx_deriving_runtime.unit) ->
  Ppx_deriving_runtime.Format.formatter ->
  ('a, 'b, 'c, 'd) tuple4 -> Ppx_deriving_runtime.unit
val show_tuple4 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'c -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'd -> Ppx_deriving_runtime.unit) ->
  ('a, 'b, 'c, 'd) tuple4 -> Ppx_deriving_runtime.string
val uu___is_Mktuple4 : 'a -> bool
val __proj__Mktuple4__item___1 : 'a * 'b * 'c * 'd -> 'a
val __proj__Mktuple4__item___2 : 'a * 'b * 'c * 'd -> 'b
val __proj__Mktuple4__item___3 : 'a * 'b * 'c * 'd -> 'c
val __proj__Mktuple4__item___4 : 'a * 'b * 'c * 'd -> 'd
type ('a, 'b, 'c, 'd, 'e) tuple5 = 'a * 'b * 'c * 'd * 'e
val tuple5_to_yojson :
  ('a -> Yojson.Safe.t) ->
  ('b -> Yojson.Safe.t) ->
  ('c -> Yojson.Safe.t) ->
  ('d -> Yojson.Safe.t) ->
  ('e -> Yojson.Safe.t) -> ('a, 'b, 'c, 'd, 'e) tuple5 -> Yojson.Safe.t
val tuple5_of_yojson :
  (Yojson.Safe.t -> 'a Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'b Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'c Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'd Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'e Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t ->
  ('a, 'b, 'c, 'd, 'e) tuple5 Ppx_deriving_yojson_runtime.error_or
val pp_tuple5 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'c -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'd -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'e -> Ppx_deriving_runtime.unit) ->
  Ppx_deriving_runtime.Format.formatter ->
  ('a, 'b, 'c, 'd, 'e) tuple5 -> Ppx_deriving_runtime.unit
val show_tuple5 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'c -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'd -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'e -> Ppx_deriving_runtime.unit) ->
  ('a, 'b, 'c, 'd, 'e) tuple5 -> Ppx_deriving_runtime.string
val uu___is_Mktuple5 : 'a -> bool
val __proj__Mktuple5__item___1 : 'a * 'b * 'c * 'd * 'e -> 'a
val __proj__Mktuple5__item___2 : 'a * 'b * 'c * 'd * 'e -> 'b
val __proj__Mktuple5__item___3 : 'a * 'b * 'c * 'd * 'e -> 'c
val __proj__Mktuple5__item___4 : 'a * 'b * 'c * 'd * 'e -> 'd
val __proj__Mktuple5__item___5 : 'a * 'b * 'c * 'd * 'e -> 'e
type ('a, 'b, 'c, 'd, 'e, 'f) tuple6 = 'a * 'b * 'c * 'd * 'e * 'f
val tuple6_to_yojson :
  ('a -> Yojson.Safe.t) ->
  ('b -> Yojson.Safe.t) ->
  ('c -> Yojson.Safe.t) ->
  ('d -> Yojson.Safe.t) ->
  ('e -> Yojson.Safe.t) ->
  ('f -> Yojson.Safe.t) -> ('a, 'b, 'c, 'd, 'e, 'f) tuple6 -> Yojson.Safe.t
val tuple6_of_yojson :
  (Yojson.Safe.t -> 'a Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'b Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'c Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'd Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'e Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'f Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t ->
  ('a, 'b, 'c, 'd, 'e, 'f) tuple6 Ppx_deriving_yojson_runtime.error_or
val pp_tuple6 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'c -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'd -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'e -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'f -> Ppx_deriving_runtime.unit) ->
  Ppx_deriving_runtime.Format.formatter ->
  ('a, 'b, 'c, 'd, 'e, 'f) tuple6 -> Ppx_deriving_runtime.unit
val show_tuple6 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'c -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'd -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'e -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'f -> Ppx_deriving_runtime.unit) ->
  ('a, 'b, 'c, 'd, 'e, 'f) tuple6 -> Ppx_deriving_runtime.string
val uu___is_Mktuple6 : 'a -> bool
val __proj__Mktuple6__item___1 : 'a * 'b * 'c * 'd * 'e * 'f -> 'a
val __proj__Mktuple6__item___2 : 'a * 'b * 'c * 'd * 'e * 'f -> 'b
val __proj__Mktuple6__item___3 : 'a * 'b * 'c * 'd * 'e * 'f -> 'c
val __proj__Mktuple6__item___4 : 'a * 'b * 'c * 'd * 'e * 'f -> 'd
val __proj__Mktuple6__item___5 : 'a * 'b * 'c * 'd * 'e * 'f -> 'e
val __proj__Mktuple6__item___6 : 'a * 'b * 'c * 'd * 'e * 'f -> 'f
type ('a, 'b, 'c, 'd, 'e, 'f, 'g) tuple7 = 'a * 'b * 'c * 'd * 'e * 'f * 'g
val tuple7_to_yojson :
  ('a -> Yojson.Safe.t) ->
  ('b -> Yojson.Safe.t) ->
  ('c -> Yojson.Safe.t) ->
  ('d -> Yojson.Safe.t) ->
  ('e -> Yojson.Safe.t) ->
  ('f -> Yojson.Safe.t) ->
  ('g -> Yojson.Safe.t) ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) tuple7 -> Yojson.Safe.t
val tuple7_of_yojson :
  (Yojson.Safe.t -> 'a Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'b Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'c Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'd Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'e Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'f Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'g Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) tuple7 Ppx_deriving_yojson_runtime.error_or
val pp_tuple7 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'c -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'd -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'e -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'f -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'g -> Ppx_deriving_runtime.unit) ->
  Ppx_deriving_runtime.Format.formatter ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) tuple7 -> Ppx_deriving_runtime.unit
val show_tuple7 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'c -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'd -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'e -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'f -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'g -> Ppx_deriving_runtime.unit) ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g) tuple7 -> Ppx_deriving_runtime.string
val uu___is_Mktuple7 : 'a -> bool
val __proj__Mktuple7__item___1 : 'a * 'b * 'c * 'd * 'e * 'f * 'g -> 'a
val __proj__Mktuple7__item___2 : 'a * 'b * 'c * 'd * 'e * 'f * 'g -> 'b
val __proj__Mktuple7__item___3 : 'a * 'b * 'c * 'd * 'e * 'f * 'g -> 'c
val __proj__Mktuple7__item___4 : 'a * 'b * 'c * 'd * 'e * 'f * 'g -> 'd
val __proj__Mktuple7__item___5 : 'a * 'b * 'c * 'd * 'e * 'f * 'g -> 'e
val __proj__Mktuple7__item___6 : 'a * 'b * 'c * 'd * 'e * 'f * 'g -> 'f
val __proj__Mktuple7__item___7 : 'a * 'b * 'c * 'd * 'e * 'f * 'g -> 'g
type ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h) tuple8 =
    'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h
val tuple8_to_yojson :
  ('a -> Yojson.Safe.t) ->
  ('b -> Yojson.Safe.t) ->
  ('c -> Yojson.Safe.t) ->
  ('d -> Yojson.Safe.t) ->
  ('e -> Yojson.Safe.t) ->
  ('f -> Yojson.Safe.t) ->
  ('g -> Yojson.Safe.t) ->
  ('h -> Yojson.Safe.t) ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h) tuple8 -> Yojson.Safe.t
val tuple8_of_yojson :
  (Yojson.Safe.t -> 'a Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'b Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'c Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'd Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'e Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'f Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'g Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'h Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h) tuple8
  Ppx_deriving_yojson_runtime.error_or
val pp_tuple8 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'c -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'd -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'e -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'f -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'g -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'h -> Ppx_deriving_runtime.unit) ->
  Ppx_deriving_runtime.Format.formatter ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h) tuple8 -> Ppx_deriving_runtime.unit
val show_tuple8 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'c -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'd -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'e -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'f -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'g -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'h -> Ppx_deriving_runtime.unit) ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h) tuple8 -> Ppx_deriving_runtime.string
val uu___is_Mktuple8 : 'a -> bool
val __proj__Mktuple8__item___1 : 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h -> 'a
val __proj__Mktuple8__item___2 : 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h -> 'b
val __proj__Mktuple8__item___3 : 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h -> 'c
val __proj__Mktuple8__item___4 : 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h -> 'd
val __proj__Mktuple8__item___5 : 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h -> 'e
val __proj__Mktuple8__item___6 : 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h -> 'f
val __proj__Mktuple8__item___7 : 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h -> 'g
val __proj__Mktuple8__item___8 : 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h -> 'h
type ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i) tuple9 =
    'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i
val tuple9_to_yojson :
  ('a -> Yojson.Safe.t) ->
  ('b -> Yojson.Safe.t) ->
  ('c -> Yojson.Safe.t) ->
  ('d -> Yojson.Safe.t) ->
  ('e -> Yojson.Safe.t) ->
  ('f -> Yojson.Safe.t) ->
  ('g -> Yojson.Safe.t) ->
  ('h -> Yojson.Safe.t) ->
  ('i -> Yojson.Safe.t) ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i) tuple9 -> Yojson.Safe.t
val tuple9_of_yojson :
  (Yojson.Safe.t -> 'a Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'b Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'c Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'd Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'e Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'f Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'g Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'h Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'i Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i) tuple9
  Ppx_deriving_yojson_runtime.error_or
val pp_tuple9 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'c -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'd -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'e -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'f -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'g -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'h -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'i -> Ppx_deriving_runtime.unit) ->
  Ppx_deriving_runtime.Format.formatter ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i) tuple9 -> Ppx_deriving_runtime.unit
val show_tuple9 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'c -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'd -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'e -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'f -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'g -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'h -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'i -> Ppx_deriving_runtime.unit) ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i) tuple9 -> Ppx_deriving_runtime.string
val uu___is_Mktuple9 : 'a -> bool
val __proj__Mktuple9__item___1 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i -> 'a
val __proj__Mktuple9__item___2 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i -> 'b
val __proj__Mktuple9__item___3 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i -> 'c
val __proj__Mktuple9__item___4 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i -> 'd
val __proj__Mktuple9__item___5 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i -> 'e
val __proj__Mktuple9__item___6 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i -> 'f
val __proj__Mktuple9__item___7 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i -> 'g
val __proj__Mktuple9__item___8 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i -> 'h
val __proj__Mktuple9__item___9 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i -> 'i
type ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j) tuple10 =
    'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j
val tuple10_to_yojson :
  ('a -> Yojson.Safe.t) ->
  ('b -> Yojson.Safe.t) ->
  ('c -> Yojson.Safe.t) ->
  ('d -> Yojson.Safe.t) ->
  ('e -> Yojson.Safe.t) ->
  ('f -> Yojson.Safe.t) ->
  ('g -> Yojson.Safe.t) ->
  ('h -> Yojson.Safe.t) ->
  ('i -> Yojson.Safe.t) ->
  ('j -> Yojson.Safe.t) ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j) tuple10 -> Yojson.Safe.t
val tuple10_of_yojson :
  (Yojson.Safe.t -> 'a Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'b Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'c Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'd Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'e Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'f Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'g Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'h Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'i Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'j Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j) tuple10
  Ppx_deriving_yojson_runtime.error_or
val pp_tuple10 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'c -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'd -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'e -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'f -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'g -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'h -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'i -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'j -> Ppx_deriving_runtime.unit) ->
  Ppx_deriving_runtime.Format.formatter ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j) tuple10 ->
  Ppx_deriving_runtime.unit
val show_tuple10 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'c -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'd -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'e -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'f -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'g -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'h -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'i -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'j -> Ppx_deriving_runtime.unit) ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j) tuple10 ->
  Ppx_deriving_runtime.string
val uu___is_Mktuple10 : 'a -> bool
val __proj__Mktuple10__item___1 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j -> 'a
val __proj__Mktuple10__item___2 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j -> 'b
val __proj__Mktuple10__item___3 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j -> 'c
val __proj__Mktuple10__item___4 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j -> 'd
val __proj__Mktuple10__item___5 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j -> 'e
val __proj__Mktuple10__item___6 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j -> 'f
val __proj__Mktuple10__item___7 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j -> 'g
val __proj__Mktuple10__item___8 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j -> 'h
val __proj__Mktuple10__item___9 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j -> 'i
val __proj__Mktuple10__item___10 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j -> 'j
type ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k) tuple11 =
    'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k
val tuple11_to_yojson :
  ('a -> Yojson.Safe.t) ->
  ('b -> Yojson.Safe.t) ->
  ('c -> Yojson.Safe.t) ->
  ('d -> Yojson.Safe.t) ->
  ('e -> Yojson.Safe.t) ->
  ('f -> Yojson.Safe.t) ->
  ('g -> Yojson.Safe.t) ->
  ('h -> Yojson.Safe.t) ->
  ('i -> Yojson.Safe.t) ->
  ('j -> Yojson.Safe.t) ->
  ('k -> Yojson.Safe.t) ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k) tuple11 -> Yojson.Safe.t
val tuple11_of_yojson :
  (Yojson.Safe.t -> 'a Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'b Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'c Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'd Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'e Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'f Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'g Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'h Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'i Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'j Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'k Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k) tuple11
  Ppx_deriving_yojson_runtime.error_or
val pp_tuple11 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'c -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'd -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'e -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'f -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'g -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'h -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'i -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'j -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'k -> Ppx_deriving_runtime.unit) ->
  Ppx_deriving_runtime.Format.formatter ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k) tuple11 ->
  Ppx_deriving_runtime.unit
val show_tuple11 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'c -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'd -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'e -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'f -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'g -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'h -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'i -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'j -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'k -> Ppx_deriving_runtime.unit) ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k) tuple11 ->
  Ppx_deriving_runtime.string
val uu___is_Mktuple11 : 'a -> bool
val __proj__Mktuple11__item___1 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k -> 'a
val __proj__Mktuple11__item___2 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k -> 'b
val __proj__Mktuple11__item___3 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k -> 'c
val __proj__Mktuple11__item___4 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k -> 'd
val __proj__Mktuple11__item___5 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k -> 'e
val __proj__Mktuple11__item___6 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k -> 'f
val __proj__Mktuple11__item___7 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k -> 'g
val __proj__Mktuple11__item___8 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k -> 'h
val __proj__Mktuple11__item___9 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k -> 'i
val __proj__Mktuple11__item___10 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k -> 'j
val __proj__Mktuple11__item___11 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k -> 'k
type ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l) tuple12 =
    'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l
val tuple12_to_yojson :
  ('a -> Yojson.Safe.t) ->
  ('b -> Yojson.Safe.t) ->
  ('c -> Yojson.Safe.t) ->
  ('d -> Yojson.Safe.t) ->
  ('e -> Yojson.Safe.t) ->
  ('f -> Yojson.Safe.t) ->
  ('g -> Yojson.Safe.t) ->
  ('h -> Yojson.Safe.t) ->
  ('i -> Yojson.Safe.t) ->
  ('j -> Yojson.Safe.t) ->
  ('k -> Yojson.Safe.t) ->
  ('l -> Yojson.Safe.t) ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l) tuple12 -> Yojson.Safe.t
val tuple12_of_yojson :
  (Yojson.Safe.t -> 'a Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'b Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'c Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'd Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'e Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'f Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'g Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'h Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'i Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'j Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'k Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'l Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l) tuple12
  Ppx_deriving_yojson_runtime.error_or
val pp_tuple12 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'c -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'd -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'e -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'f -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'g -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'h -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'i -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'j -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'k -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'l -> Ppx_deriving_runtime.unit) ->
  Ppx_deriving_runtime.Format.formatter ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l) tuple12 ->
  Ppx_deriving_runtime.unit
val show_tuple12 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'c -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'd -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'e -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'f -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'g -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'h -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'i -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'j -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'k -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'l -> Ppx_deriving_runtime.unit) ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l) tuple12 ->
  Ppx_deriving_runtime.string
val uu___is_Mktuple12 : 'a -> bool
val __proj__Mktuple12__item___1 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l -> 'a
val __proj__Mktuple12__item___2 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l -> 'b
val __proj__Mktuple12__item___3 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l -> 'c
val __proj__Mktuple12__item___4 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l -> 'd
val __proj__Mktuple12__item___5 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l -> 'e
val __proj__Mktuple12__item___6 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l -> 'f
val __proj__Mktuple12__item___7 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l -> 'g
val __proj__Mktuple12__item___8 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l -> 'h
val __proj__Mktuple12__item___9 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l -> 'i
val __proj__Mktuple12__item___10 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l -> 'j
val __proj__Mktuple12__item___11 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l -> 'k
val __proj__Mktuple12__item___12 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l -> 'l
type ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm) tuple13 =
    'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm
val tuple13_to_yojson :
  ('a -> Yojson.Safe.t) ->
  ('b -> Yojson.Safe.t) ->
  ('c -> Yojson.Safe.t) ->
  ('d -> Yojson.Safe.t) ->
  ('e -> Yojson.Safe.t) ->
  ('f -> Yojson.Safe.t) ->
  ('g -> Yojson.Safe.t) ->
  ('h -> Yojson.Safe.t) ->
  ('i -> Yojson.Safe.t) ->
  ('j -> Yojson.Safe.t) ->
  ('k -> Yojson.Safe.t) ->
  ('l -> Yojson.Safe.t) ->
  ('m -> Yojson.Safe.t) ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm) tuple13 ->
  Yojson.Safe.t
val tuple13_of_yojson :
  (Yojson.Safe.t -> 'a Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'b Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'c Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'd Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'e Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'f Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'g Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'h Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'i Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'j Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'k Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'l Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'm Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm) tuple13
  Ppx_deriving_yojson_runtime.error_or
val pp_tuple13 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'c -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'd -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'e -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'f -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'g -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'h -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'i -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'j -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'k -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'l -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'm -> Ppx_deriving_runtime.unit) ->
  Ppx_deriving_runtime.Format.formatter ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm) tuple13 ->
  Ppx_deriving_runtime.unit
val show_tuple13 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'c -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'd -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'e -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'f -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'g -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'h -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'i -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'j -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'k -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'l -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'm -> Ppx_deriving_runtime.unit) ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm) tuple13 ->
  Ppx_deriving_runtime.string
val uu___is_Mktuple13 : 'a -> bool
val __proj__Mktuple13__item___1 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm -> 'a
val __proj__Mktuple13__item___2 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm -> 'b
val __proj__Mktuple13__item___3 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm -> 'c
val __proj__Mktuple13__item___4 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm -> 'd
val __proj__Mktuple13__item___5 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm -> 'e
val __proj__Mktuple13__item___6 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm -> 'f
val __proj__Mktuple13__item___7 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm -> 'g
val __proj__Mktuple13__item___8 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm -> 'h
val __proj__Mktuple13__item___9 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm -> 'i
val __proj__Mktuple13__item___10 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm -> 'j
val __proj__Mktuple13__item___11 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm -> 'k
val __proj__Mktuple13__item___12 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm -> 'l
val __proj__Mktuple13__item___13 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm -> 'm
type ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n) tuple14 =
    'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm * 'n
val tuple14_to_yojson :
  ('a -> Yojson.Safe.t) ->
  ('b -> Yojson.Safe.t) ->
  ('c -> Yojson.Safe.t) ->
  ('d -> Yojson.Safe.t) ->
  ('e -> Yojson.Safe.t) ->
  ('f -> Yojson.Safe.t) ->
  ('g -> Yojson.Safe.t) ->
  ('h -> Yojson.Safe.t) ->
  ('i -> Yojson.Safe.t) ->
  ('j -> Yojson.Safe.t) ->
  ('k -> Yojson.Safe.t) ->
  ('l -> Yojson.Safe.t) ->
  ('m -> Yojson.Safe.t) ->
  ('n -> Yojson.Safe.t) ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n) tuple14 ->
  Yojson.Safe.t
val tuple14_of_yojson :
  (Yojson.Safe.t -> 'a Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'b Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'c Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'd Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'e Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'f Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'g Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'h Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'i Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'j Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'k Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'l Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'm Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'n Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n) tuple14
  Ppx_deriving_yojson_runtime.error_or
val _ :
  (Yojson.Safe.t -> 'a Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'b Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'c Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'd Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'e Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'f Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'g Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'h Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'i Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'j Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'k Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'l Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'm Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'n Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n) tuple14
  Ppx_deriving_yojson_runtime.error_or
val pp_tuple14 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'c -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'd -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'e -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'f -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'g -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'h -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'i -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'j -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'k -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'l -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'm -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'n -> Ppx_deriving_runtime.unit) ->
  Ppx_deriving_runtime.Format.formatter ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n) tuple14 ->
  Ppx_deriving_runtime.unit
val show_tuple14 :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'b -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'c -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'd -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'e -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'f -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'g -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'h -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'i -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'j -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'k -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'l -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'm -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'n -> Ppx_deriving_runtime.unit) ->
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n) tuple14 ->
  Ppx_deriving_runtime.string
val uu___is_Mktuple14 : 'a -> bool
val __proj__Mktuple14__item___1 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm * 'n -> 'a
val __proj__Mktuple14__item___2 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm * 'n -> 'b
val __proj__Mktuple14__item___3 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm * 'n -> 'c
val __proj__Mktuple14__item___4 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm * 'n -> 'd
val __proj__Mktuple14__item___5 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm * 'n -> 'e
val __proj__Mktuple14__item___6 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm * 'n -> 'f
val __proj__Mktuple14__item___7 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm * 'n -> 'g
val __proj__Mktuple14__item___8 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm * 'n -> 'h
val __proj__Mktuple14__item___9 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm * 'n -> 'i
val __proj__Mktuple14__item___10 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm * 'n -> 'j
val __proj__Mktuple14__item___11 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm * 'n -> 'k
val __proj__Mktuple14__item___12 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm * 'n -> 'l
val __proj__Mktuple14__item___13 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm * 'n -> 'm
val __proj__Mktuple14__item___14 :
  'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k * 'l * 'm * 'n -> 'n

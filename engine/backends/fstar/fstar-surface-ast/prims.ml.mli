type int = Z.t
val pp_int :
  Ppx_deriving_runtime.Format.formatter -> int -> Ppx_deriving_runtime.unit
val show_int : int -> Ppx_deriving_runtime.string
val of_int : int/2 -> Z.t
val int_zero : Z.t
val int_one : Z.t
val parse_int : string -> Z.t
val to_string : Z.t -> string
type tmp = string
val tmp_to_yojson : tmp -> Yojson.Safe.t
val tmp_of_yojson : Yojson.Safe.t -> tmp Ppx_deriving_yojson_runtime.error_or
val int_to_yojson : Z.t -> Yojson.Safe.t
val int_of_yojson : Yojson.Safe.t -> (Z.t, string) result
type attribute = unit
val cps : attribute
type 'Auu____5 hasEq = unit
type eqtype = unit
type bool' = bool
val bool'_to_yojson : bool' -> Yojson.Safe.t
val bool'_of_yojson :
  Yojson.Safe.t -> bool' Ppx_deriving_yojson_runtime.error_or
val pp_bool' :
  Ppx_deriving_runtime.Format.formatter -> bool' -> Ppx_deriving_runtime.unit
val show_bool' : bool' -> Ppx_deriving_runtime.string
type bool = bool'
val bool_to_yojson : bool -> Yojson.Safe.t
val bool_of_yojson :
  Yojson.Safe.t -> bool Ppx_deriving_yojson_runtime.error_or
val pp_bool :
  Ppx_deriving_runtime.Format.formatter -> bool -> Ppx_deriving_runtime.unit
val show_bool : bool -> Ppx_deriving_runtime.string
type empty = unit
type trivial = T
val uu___is_T : trivial -> bool
type nonrec unit = unit
type 'Ap squash = unit
type 'Ap auto_squash = unit
type l_True = unit
type l_False = unit
type ('Aa, 'Ax, 'dummyV0) equals = Refl
val uu___is_Refl : 'Aa -> 'Aa -> ('Aa, unit, unit) equals -> bool
type ('Aa, 'Ax, 'Ay) eq2 = unit
type ('Aa, 'Ab, 'Ax, 'Ay) op_Equals_Equals_Equals = unit
type 'Ab b2t = unit
type ('Ap, 'Aq) pair = Pair of 'Ap * 'Aq
val uu___is_Pair : ('Ap, 'Aq) pair -> bool
val __proj__Pair__item___1 : ('Ap, 'Aq) pair -> 'Ap
val __proj__Pair__item___2 : ('Ap, 'Aq) pair -> 'Aq
type ('Ap, 'Aq) l_and = unit
type ('Ap, 'Aq) sum = Left of 'Ap | Right of 'Aq
val uu___is_Left : ('Ap, 'Aq) sum -> bool
val __proj__Left__item___0 : ('Ap, 'Aq) sum -> 'Ap
val uu___is_Right : ('Ap, 'Aq) sum -> bool
val __proj__Right__item___0 : ('Ap, 'Aq) sum -> 'Aq
type ('Ap, 'Aq) l_or = unit
type ('Ap, 'Aq) l_imp = unit
type ('Ap, 'Aq) l_iff = unit
type 'Ap l_not = unit
type ('Ap, 'Aq, 'Ar) l_ITE = unit
type ('Aa, 'Ab, 'Auu____484, 'Auu____485) precedes = unit
type ('Aa, 'Auu____490, 'Auu____491) has_type = unit
type ('Aa, 'Ap) l_Forall = unit
type prop = unit
val id : 'a -> 'a
type ('Aa, 'Ab) dtuple2 = Mkdtuple2 of 'Aa * 'Ab
val uu___is_Mkdtuple2 : ('Aa, 'Ab) dtuple2 -> bool
val __proj__Mkdtuple2__item___1 : ('Aa, 'Ab) dtuple2 -> 'Aa
val __proj__Mkdtuple2__item___2 : ('Aa, 'Ab) dtuple2 -> 'Ab
type ('Aa, 'Ap) l_Exists = unit
type _pos = int * int
type _rng = string * _pos * _pos
type range = _rng * _rng
type string' = string
val string'_to_yojson : string' -> Yojson.Safe.t
val string'_of_yojson :
  Yojson.Safe.t -> string' Ppx_deriving_yojson_runtime.error_or
val pp_string' :
  Ppx_deriving_runtime.Format.formatter ->
  string' -> Ppx_deriving_runtime.unit
val show_string' : string' -> Ppx_deriving_runtime.string
type string = string'
val string_to_yojson : string -> Yojson.Safe.t
val string_of_yojson :
  Yojson.Safe.t -> string Ppx_deriving_yojson_runtime.error_or
val pp_string :
  Ppx_deriving_runtime.Format.formatter ->
  string -> Ppx_deriving_runtime.unit
val show_string : string -> Ppx_deriving_runtime.string
type pure_pre = unit
type ('Aa, 'Apre) pure_post' = unit
type 'Aa pure_post = unit
type 'Aa pure_wp = unit
type 'Auu____655 guard_free = unit
type ('Aa, 'Ax, 'Ap) pure_return = unit
type ('Ar1, 'Aa, 'Ab, 'Awp1, 'Awp2, 'Ap) pure_bind_wp = 'Awp1
type ('Aa, 'Ap, 'Awp_then, 'Awp_else, 'Apost) pure_if_then_else = unit
val pure_if_then_else_to_yojson :
  ('Aa -> Yojson.Safe.t) ->
  ('Ap -> Yojson.Safe.t) ->
  ('Awp_then -> Yojson.Safe.t) ->
  ('Awp_else -> Yojson.Safe.t) ->
  ('Apost -> Yojson.Safe.t) ->
  ('Aa, 'Ap, 'Awp_then, 'Awp_else, 'Apost) pure_if_then_else -> Yojson.Safe.t
val pure_if_then_else_of_yojson :
  (Yojson.Safe.t -> 'Aa Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'Ap Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'Awp_then Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'Awp_else Ppx_deriving_yojson_runtime.error_or) ->
  (Yojson.Safe.t -> 'Apost Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t ->
  ('Aa, 'Ap, 'Awp_then, 'Awp_else, 'Apost) pure_if_then_else
  Ppx_deriving_yojson_runtime.error_or
val pp_pure_if_then_else :
  (Ppx_deriving_runtime.Format.formatter -> 'Aa -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'Ap -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter ->
   'Awp_then -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter ->
   'Awp_else -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter ->
   'Apost -> Ppx_deriving_runtime.unit) ->
  Ppx_deriving_runtime.Format.formatter ->
  ('Aa, 'Ap, 'Awp_then, 'Awp_else, 'Apost) pure_if_then_else ->
  Ppx_deriving_runtime.unit
val show_pure_if_then_else :
  (Ppx_deriving_runtime.Format.formatter -> 'Aa -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter -> 'Ap -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter ->
   'Awp_then -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter ->
   'Awp_else -> Ppx_deriving_runtime.unit) ->
  (Ppx_deriving_runtime.Format.formatter ->
   'Apost -> Ppx_deriving_runtime.unit) ->
  ('Aa, 'Ap, 'Awp_then, 'Awp_else, 'Apost) pure_if_then_else ->
  Ppx_deriving_runtime.string
type ('Aa, 'Awp, 'Apost) pure_ite_wp = unit
type ('Aa, 'Awp1, 'Awp2) pure_stronger = unit
type ('Aa, 'Ab, 'Awp, 'Ap) pure_close_wp = unit
type ('Aa, 'Aq, 'Awp, 'Ap) pure_assert_p = unit
type ('Aa, 'Aq, 'Awp, 'Ap) pure_assume_p = unit
type ('Aa, 'Ap) pure_null_wp = unit
type ('Aa, 'Awp) pure_trivial = 'Awp
type ('Ap, 'Apost) pure_assert_wp = unit
type ('Aa, 'Awp, 'Auu____878) purewp_id = 'Awp
val mk_range : string/2 -> int -> int -> int -> int -> range
val range_0 : range
val op_AmpAmp : bool/2 -> bool/2 -> bool/2
val op_BarBar : bool/2 -> bool/2 -> bool/2
val op_Negation : bool/2 -> bool/2
val ( + ) : Z.t -> Z.t -> Z.t
val ( - ) : Z.t -> Z.t -> Z.t
val ( * ) : Z.t -> Z.t -> Z.t
val ( / ) : Z.t -> Z.t -> Z.t
val ( <= ) : Z.t -> Z.t -> bool/2
val ( >= ) : Z.t -> Z.t -> bool/2
val ( < ) : Z.t -> Z.t -> bool/2
val ( > ) : Z.t -> Z.t -> bool/2
val ( mod ) : Z.t -> Z.t -> Z.t
val ( ~- ) : Z.t -> Z.t
val op_Multiply : Z.t -> Z.t -> Z.t
val op_Subtraction : Z.t -> Z.t -> Z.t
val op_Addition : Z.t -> Z.t -> Z.t
val op_Minus : Z.t -> Z.t
val op_LessThan : Z.t -> Z.t -> bool/2
val op_LessThanOrEqual : Z.t -> Z.t -> bool/2
val op_GreaterThan : Z.t -> Z.t -> bool/2
val op_GreaterThanOrEqual : Z.t -> Z.t -> bool/2
val op_Equality : 'a -> 'a -> bool/2
val op_disEquality : 'a -> 'a -> bool/2
type nonrec exn = exn
type 'a array' = 'a array
val array'_to_yojson : ('a -> Yojson.Safe.t) -> 'a array' -> Yojson.Safe.t
val array'_of_yojson :
  (Yojson.Safe.t -> 'a Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t -> 'a array' Ppx_deriving_yojson_runtime.error_or
val pp_array' :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  Ppx_deriving_runtime.Format.formatter ->
  'a array' -> Ppx_deriving_runtime.unit
val show_array' :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  'a array' -> Ppx_deriving_runtime.string
type 'a array = 'a array'
val array_to_yojson : ('a -> Yojson.Safe.t) -> 'a array -> Yojson.Safe.t
val array_of_yojson :
  (Yojson.Safe.t -> 'a Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t -> 'a array Ppx_deriving_yojson_runtime.error_or
val pp_array :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  Ppx_deriving_runtime.Format.formatter ->
  'a array -> Ppx_deriving_runtime.unit
val show_array :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  'a array -> Ppx_deriving_runtime.string
val strcat : string/2 -> string/2 -> string/2
val op_Hat : string/2 -> string/2 -> string/2
type 'a list' = 'a list
val list'_to_yojson : ('a -> Yojson.Safe.t) -> 'a list' -> Yojson.Safe.t
val list'_of_yojson :
  (Yojson.Safe.t -> 'a Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t -> 'a list' Ppx_deriving_yojson_runtime.error_or
val pp_list' :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  Ppx_deriving_runtime.Format.formatter ->
  'a list' -> Ppx_deriving_runtime.unit
val show_list' :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  'a list' -> Ppx_deriving_runtime.string
type 'a list = 'a list'
val list_to_yojson : ('a -> Yojson.Safe.t) -> 'a list -> Yojson.Safe.t
val list_of_yojson :
  (Yojson.Safe.t -> 'a Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t -> 'a list Ppx_deriving_yojson_runtime.error_or
val _ :
  (Yojson.Safe.t -> 'a Ppx_deriving_yojson_runtime.error_or) ->
  Yojson.Safe.t -> 'a list Ppx_deriving_yojson_runtime.error_or
val pp_list :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  Ppx_deriving_runtime.Format.formatter ->
  'a list -> Ppx_deriving_runtime.unit
val show_list :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  'a list -> Ppx_deriving_runtime.string
val uu___is_Nil : 'Aa list -> bool
val uu___is_Cons : 'Aa list -> bool
val __proj__Cons__item__hd : 'Aa list -> 'Aa
val __proj__Cons__item__tl : 'Aa list -> 'Aa list
type pattern = unit
type ('Aa, 'Auu____1278) decreases = unit
val returnM : 'Aa -> 'Aa
type lex_t = LexTop | LexCons of unit * Obj.t * lex_t
val uu___is_LexTop : lex_t -> bool
val uu___is_LexCons : lex_t -> bool
type 'Aprojectee __proj__LexCons__item__a = Obj.t
val __proj__LexCons__item___1 : lex_t -> Obj.t
val __proj__LexCons__item___2 : lex_t -> lex_t
type ('Aa, 'Awp) as_requires = 'Awp
type ('Aa, 'Awp, 'Ax) as_ensures = unit
val admit : unit/2 -> 'a
val magic : unit/2 -> 'a
val unsafe_coerce : 'Aa -> 'Ab
type 'Ap spinoff = 'Ap
type nat = int
type pos = int
type nonzero = int
val op_Modulus : Z.t -> Z.t -> Z.t
val op_Division : Z.t -> Z.t -> Z.t
val pow2 : nat -> pos
val min : int -> int -> int
val abs : int -> int
val string_of_bool : bool/2 -> string/2
val string_of_int : Z.t -> string/2
type ('Ar, 'Amsg, 'Ab) labeled = 'Ab

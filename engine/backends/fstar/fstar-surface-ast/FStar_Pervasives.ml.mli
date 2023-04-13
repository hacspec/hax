type pattern = Prims.unit
type eqtype_u = Prims.unit
type 'p spinoff = 'p
val id : 'a -> 'a
type ('a, 'uuuuu) trivial_pure_post = Prims.unit
type ('uuuuu, 'uuuuu1) ambient = Prims.unit
val normalize_term : 'uuuuu -> 'uuuuu
type 'a normalize = 'a
type norm_step =
    Simpl
  | Weak
  | HNF
  | Primops
  | Delta
  | Zeta
  | ZetaFull
  | Iota
  | NBE
  | Reify
  | UnfoldOnly of Prims.string Prims.list
  | UnfoldFully of Prims.string Prims.list
  | UnfoldAttr of Prims.string Prims.list
  | UnfoldQual of Prims.string Prims.list
  | UnfoldNamespace of Prims.string Prims.list
  | Unmeta
  | Unascribe
val uu___is_Simpl : norm_step -> Prims.bool
val uu___is_Weak : norm_step -> Prims.bool
val uu___is_HNF : norm_step -> Prims.bool
val uu___is_Primops : norm_step -> Prims.bool
val uu___is_Delta : norm_step -> Prims.bool
val uu___is_Zeta : norm_step -> Prims.bool
val uu___is_ZetaFull : norm_step -> Prims.bool
val uu___is_Iota : norm_step -> Prims.bool
val uu___is_NBE : norm_step -> Prims.bool
val uu___is_Reify : norm_step -> Prims.bool
val uu___is_UnfoldOnly : norm_step -> Prims.bool
val __proj__UnfoldOnly__item___0 : norm_step -> Prims.string Prims.list
val uu___is_UnfoldFully : norm_step -> Prims.bool
val __proj__UnfoldFully__item___0 : norm_step -> Prims.string Prims.list
val uu___is_UnfoldAttr : norm_step -> Prims.bool
val __proj__UnfoldAttr__item___0 : norm_step -> Prims.string Prims.list
val uu___is_UnfoldQual : norm_step -> Prims.bool
val __proj__UnfoldQual__item___0 : norm_step -> Prims.string Prims.list
val uu___is_UnfoldNamespace : norm_step -> Prims.bool
val __proj__UnfoldNamespace__item___0 : norm_step -> Prims.string Prims.list
val uu___is_Unmeta : norm_step -> Prims.bool
val uu___is_Unascribe : norm_step -> Prims.bool
val simplify : norm_step
val weak : norm_step
val hnf : norm_step
val primops : norm_step
val delta : norm_step
val zeta : norm_step
val zeta_full : norm_step
val iota : norm_step
val nbe : norm_step
val reify_ : norm_step
val delta_only : Prims.string Prims.list -> norm_step
val delta_fully : Prims.string Prims.list -> norm_step
val delta_attr : Prims.string Prims.list -> norm_step
val delta_qualifier : Prims.string Prims.list -> norm_step
val delta_namespace : Prims.string Prims.list -> norm_step
val unmeta : norm_step
val unascribe : norm_step
val norm : norm_step Prims.list -> Prims.unit -> Obj.t -> Obj.t
type ('a, 'x, 'uuuuu) pure_return = Prims.unit
type ('a, 'b, 'wp1, 'wp2, 'uuuuu) pure_bind_wp = 'wp1
type ('a, 'p, 'wputhen, 'wpuelse, 'uuuuu) pure_if_then_else = Prims.unit
type ('a, 'wp, 'uuuuu) pure_ite_wp = Prims.unit
type ('a, 'b, 'wp, 'uuuuu) pure_close_wp = Prims.unit
type ('a, 'uuuuu) pure_null_wp = Prims.unit
type ('p, 'uuuuu) pure_assert_wp = Prims.unit
type ('p, 'uuuuu) pure_assume_wp = Prims.unit
type ('a, 'pre, 'post, 'uuuuu) div_hoare_to_wp = Prims.unit
type 'heap st_pre_h = Prims.unit
type ('heap, 'a, 'pre) st_post_h' = Prims.unit
type ('heap, 'a) st_post_h = Prims.unit
type ('heap, 'a) st_wp_h = Prims.unit
type ('heap, 'a, 'x, 'p, 'uuuuu) st_return = 'p
type ('heap, 'a, 'b, 'wp1, 'wp2, 'p, 'h0) st_bind_wp = 'wp1
type ('heap, 'a, 'p, 'wputhen, 'wpuelse, 'post, 'h0) st_if_then_else =
    Prims.unit
type ('heap, 'a, 'wp, 'post, 'h0) st_ite_wp = Prims.unit
type ('heap, 'a, 'wp1, 'wp2) st_stronger = Prims.unit
type ('heap, 'a, 'b, 'wp, 'p, 'h) st_close_wp = Prims.unit
type ('heap, 'a, 'wp) st_trivial = Prims.unit
type 'a result = V of 'a | E of Prims.exn | Err of Prims.string
val uu___is_V : 'a result -> Prims.bool
val __proj__V__item__v : 'a result -> 'a
val uu___is_E : 'a result -> Prims.bool
val __proj__E__item__e : 'a result -> Prims.exn
val uu___is_Err : 'a result -> Prims.bool
val __proj__Err__item__msg : 'a result -> Prims.string
type ex_pre = Prims.unit
type ('a, 'pre) ex_post' = Prims.unit
type 'a ex_post = Prims.unit
type 'a ex_wp = Prims.unit
type ('a, 'x, 'p) ex_return = 'p
type ('a, 'b, 'wp1, 'wp2, 'p) ex_bind_wp = Prims.unit
type ('a, 'p, 'wputhen, 'wpuelse, 'post) ex_if_then_else = Prims.unit
type ('a, 'wp, 'post) ex_ite_wp = Prims.unit
type ('a, 'wp1, 'wp2) ex_stronger = Prims.unit
type ('a, 'b, 'wp, 'p) ex_close_wp = Prims.unit
type ('a, 'wp) ex_trivial = 'wp
type ('a, 'wp, 'p) lift_div_exn = 'wp
type 'h all_pre_h = Prims.unit
type ('h, 'a, 'pre) all_post_h' = Prims.unit
type ('h, 'a) all_post_h = Prims.unit
type ('h, 'a) all_wp_h = Prims.unit
type ('heap, 'a, 'x, 'p, 'uuuuu) all_return = 'p
type ('heap, 'a, 'b, 'wp1, 'wp2, 'p, 'h0) all_bind_wp = 'wp1
type ('heap, 'a, 'p, 'wputhen, 'wpuelse, 'post, 'h0) all_if_then_else =
    Prims.unit
type ('heap, 'a, 'wp, 'post, 'h0) all_ite_wp = Prims.unit
type ('heap, 'a, 'wp1, 'wp2) all_stronger = Prims.unit
type ('heap, 'a, 'b, 'wp, 'p, 'h) all_close_wp = Prims.unit
type ('heap, 'a, 'wp) all_trivial = Prims.unit
type 'uuuuu inversion = Prims.unit
type ('a, 'b) either = Inl of 'a | Inr of 'b
val uu___is_Inl : ('a, 'b) either -> Prims.bool
val __proj__Inl__item__v : ('a, 'b) either -> 'a
val uu___is_Inr : ('a, 'b) either -> Prims.bool
val __proj__Inr__item__v : ('a, 'b) either -> 'b
val dfst : ('a, 'b) Prims.dtuple2 -> 'a
val dsnd : ('a, 'b) Prims.dtuple2 -> 'b
type ('a, 'b, 'c) dtuple3 = Mkdtuple3 of 'a * 'b * 'c
val uu___is_Mkdtuple3 : ('a, 'b, 'c) dtuple3 -> Prims.bool
val __proj__Mkdtuple3__item___1 : ('a, 'b, 'c) dtuple3 -> 'a
val __proj__Mkdtuple3__item___2 : ('a, 'b, 'c) dtuple3 -> 'b
val __proj__Mkdtuple3__item___3 : ('a, 'b, 'c) dtuple3 -> 'c
type ('a, 'b, 'c, 'd) dtuple4 = Mkdtuple4 of 'a * 'b * 'c * 'd
val uu___is_Mkdtuple4 : ('a, 'b, 'c, 'd) dtuple4 -> Prims.bool
val __proj__Mkdtuple4__item___1 : ('a, 'b, 'c, 'd) dtuple4 -> 'a
val __proj__Mkdtuple4__item___2 : ('a, 'b, 'c, 'd) dtuple4 -> 'b
val __proj__Mkdtuple4__item___3 : ('a, 'b, 'c, 'd) dtuple4 -> 'c
val __proj__Mkdtuple4__item___4 : ('a, 'b, 'c, 'd) dtuple4 -> 'd
val false_elim : Prims.unit -> 'uuuuu
type __internal_ocaml_attributes =
    PpxDerivingShow
  | PpxDerivingShowConstant of Prims.string
  | PpxDerivingYoJson
  | CInline
  | Substitute
  | Gc
  | Comment of Prims.string
  | CPrologue of Prims.string
  | CEpilogue of Prims.string
  | CConst of Prims.string
  | CCConv of Prims.string
  | CAbstractStruct
  | CIfDef
  | CMacro
val uu___is_PpxDerivingShow : __internal_ocaml_attributes -> Prims.bool
val uu___is_PpxDerivingShowConstant :
  __internal_ocaml_attributes -> Prims.bool
val __proj__PpxDerivingShowConstant__item___0 :
  __internal_ocaml_attributes -> Prims.string
val uu___is_PpxDerivingYoJson : __internal_ocaml_attributes -> Prims.bool
val uu___is_CInline : __internal_ocaml_attributes -> Prims.bool
val uu___is_Substitute : __internal_ocaml_attributes -> Prims.bool
val uu___is_Gc : __internal_ocaml_attributes -> Prims.bool
val uu___is_Comment : __internal_ocaml_attributes -> Prims.bool
val __proj__Comment__item___0 : __internal_ocaml_attributes -> Prims.string
val uu___is_CPrologue : __internal_ocaml_attributes -> Prims.bool
val __proj__CPrologue__item___0 : __internal_ocaml_attributes -> Prims.string
val uu___is_CEpilogue : __internal_ocaml_attributes -> Prims.bool
val __proj__CEpilogue__item___0 : __internal_ocaml_attributes -> Prims.string
val uu___is_CConst : __internal_ocaml_attributes -> Prims.bool
val __proj__CConst__item___0 : __internal_ocaml_attributes -> Prims.string
val uu___is_CCConv : __internal_ocaml_attributes -> Prims.bool
val __proj__CCConv__item___0 : __internal_ocaml_attributes -> Prims.string
val uu___is_CAbstractStruct : __internal_ocaml_attributes -> Prims.bool
val uu___is_CIfDef : __internal_ocaml_attributes -> Prims.bool
val uu___is_CMacro : __internal_ocaml_attributes -> Prims.bool
val singleton : 'uuuuu -> 'uuuuu
type 'a eqtype_as_type = 'a
val coerce_eq : Prims.unit -> 'a -> 'b

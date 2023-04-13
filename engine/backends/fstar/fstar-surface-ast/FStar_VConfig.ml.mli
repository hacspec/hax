type vconfig = {
  initial_fuel : Prims.int;
  max_fuel : Prims.int;
  initial_ifuel : Prims.int;
  max_ifuel : Prims.int;
  detail_errors : Prims.bool;
  detail_hint_replay : Prims.bool;
  no_smt : Prims.bool;
  quake_lo : Prims.int;
  quake_hi : Prims.int;
  quake_keep : Prims.bool;
  retry : Prims.bool;
  smtencoding_elim_box : Prims.bool;
  smtencoding_nl_arith_repr : Prims.string;
  smtencoding_l_arith_repr : Prims.string;
  smtencoding_valid_intro : Prims.bool;
  smtencoding_valid_elim : Prims.bool;
  tcnorm : Prims.bool;
  no_plugins : Prims.bool;
  no_tactics : Prims.bool;
  z3cliopt : Prims.string Prims.list;
  z3smtopt : Prims.string Prims.list;
  z3refresh : Prims.bool;
  z3rlimit : Prims.int;
  z3rlimit_factor : Prims.int;
  z3seed : Prims.int;
  trivial_pre_for_unannotated_effectful_fns : Prims.bool;
  reuse_hint_for : Prims.string FStar_Pervasives_Native.option;
}
val __proj__Mkvconfig__item__initial_fuel : vconfig -> Prims.int
val __proj__Mkvconfig__item__max_fuel : vconfig -> Prims.int
val __proj__Mkvconfig__item__initial_ifuel : vconfig -> Prims.int
val __proj__Mkvconfig__item__max_ifuel : vconfig -> Prims.int
val __proj__Mkvconfig__item__detail_errors : vconfig -> Prims.bool
val __proj__Mkvconfig__item__detail_hint_replay : vconfig -> Prims.bool
val __proj__Mkvconfig__item__no_smt : vconfig -> Prims.bool
val __proj__Mkvconfig__item__quake_lo : vconfig -> Prims.int
val __proj__Mkvconfig__item__quake_hi : vconfig -> Prims.int
val __proj__Mkvconfig__item__quake_keep : vconfig -> Prims.bool
val __proj__Mkvconfig__item__retry : vconfig -> Prims.bool
val __proj__Mkvconfig__item__smtencoding_elim_box : vconfig -> Prims.bool
val __proj__Mkvconfig__item__smtencoding_nl_arith_repr :
  vconfig -> Prims.string
val __proj__Mkvconfig__item__smtencoding_l_arith_repr :
  vconfig -> Prims.string
val __proj__Mkvconfig__item__smtencoding_valid_intro : vconfig -> Prims.bool
val __proj__Mkvconfig__item__smtencoding_valid_elim : vconfig -> Prims.bool
val __proj__Mkvconfig__item__tcnorm : vconfig -> Prims.bool
val __proj__Mkvconfig__item__no_plugins : vconfig -> Prims.bool
val __proj__Mkvconfig__item__no_tactics : vconfig -> Prims.bool
val __proj__Mkvconfig__item__z3cliopt : vconfig -> Prims.string Prims.list
val __proj__Mkvconfig__item__z3smtopt : vconfig -> Prims.string Prims.list
val __proj__Mkvconfig__item__z3refresh : vconfig -> Prims.bool
val __proj__Mkvconfig__item__z3rlimit : vconfig -> Prims.int
val __proj__Mkvconfig__item__z3rlimit_factor : vconfig -> Prims.int
val __proj__Mkvconfig__item__z3seed : vconfig -> Prims.int
val __proj__Mkvconfig__item__trivial_pre_for_unannotated_effectful_fns :
  vconfig -> Prims.bool
val __proj__Mkvconfig__item__reuse_hint_for :
  vconfig -> Prims.string FStar_Pervasives_Native.option

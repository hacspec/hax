val eq_ident : FStar_Ident.ident -> FStar_Ident.ident -> Prims.bool
val eq_list :
  ('a -> 'a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list -> Prims.bool
val eq_option :
  ('a -> 'a -> Prims.bool) ->
  'a FStar_Pervasives_Native.option ->
  'a FStar_Pervasives_Native.option -> Prims.bool
val eq_sconst : FStar_Const.sconst -> FStar_Const.sconst -> Prims.bool
val eq_term : FStar_Parser_AST.term -> FStar_Parser_AST.term -> Prims.bool
val eq_terms :
  FStar_Parser_AST.term Prims.list ->
  FStar_Parser_AST.term Prims.list -> Prims.bool
val eq_arg :
  FStar_Parser_AST.term * FStar_Parser_AST.imp ->
  FStar_Parser_AST.term * FStar_Parser_AST.imp -> Prims.bool
val eq_imp : FStar_Parser_AST.imp -> FStar_Parser_AST.imp -> Prims.bool
val eq_args :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list ->
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool
val eq_arg_qualifier :
  FStar_Parser_AST.arg_qualifier ->
  FStar_Parser_AST.arg_qualifier -> Prims.bool
val eq_pattern :
  FStar_Parser_AST.pattern -> FStar_Parser_AST.pattern -> Prims.bool
val eq_aqual :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool
val eq_pattern' :
  FStar_Parser_AST.pattern' -> FStar_Parser_AST.pattern' -> Prims.bool
val eq_term' : FStar_Parser_AST.term' -> FStar_Parser_AST.term' -> Prims.bool
val eq_calc_step :
  FStar_Parser_AST.calc_step -> FStar_Parser_AST.calc_step -> Prims.bool
val eq_binder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.binder -> Prims.bool
val eq_binder' :
  FStar_Parser_AST.binder' -> FStar_Parser_AST.binder' -> Prims.bool
val eq_match_returns_annotation :
  FStar_Ident.ident FStar_Pervasives_Native.option * FStar_Parser_AST.term *
  Prims.bool ->
  FStar_Ident.ident FStar_Pervasives_Native.option * FStar_Parser_AST.term *
  Prims.bool -> Prims.bool
val eq_branch :
  FStar_Parser_AST.pattern *
  FStar_Parser_AST.term FStar_Pervasives_Native.option *
  FStar_Parser_AST.term ->
  FStar_Parser_AST.pattern *
  FStar_Parser_AST.term FStar_Pervasives_Native.option *
  FStar_Parser_AST.term -> Prims.bool
val eq_tycon_record :
  FStar_Parser_AST.tycon_record ->
  FStar_Parser_AST.tycon_record -> Prims.bool
val eq_constructor_payload :
  FStar_Parser_AST.constructor_payload ->
  FStar_Parser_AST.constructor_payload -> Prims.bool
val eq_tycon : FStar_Parser_AST.tycon -> FStar_Parser_AST.tycon -> Prims.bool
val eq_lid : FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool
val eq_lift : FStar_Parser_AST.lift -> FStar_Parser_AST.lift -> Prims.bool
val eq_pragma :
  FStar_Parser_AST.pragma -> FStar_Parser_AST.pragma -> Prims.bool
val eq_qualifier :
  FStar_Parser_AST.qualifier -> FStar_Parser_AST.qualifier -> Prims.bool
val eq_qualifiers :
  FStar_Parser_AST.qualifiers -> FStar_Parser_AST.qualifiers -> Prims.bool
val eq_decl' : FStar_Parser_AST.decl' -> FStar_Parser_AST.decl' -> Prims.bool
val eq_effect_decl :
  FStar_Parser_AST.effect_decl -> FStar_Parser_AST.effect_decl -> Prims.bool
val eq_decl : FStar_Parser_AST.decl -> FStar_Parser_AST.decl -> Prims.bool
val concat_map :
  Prims.unit ->
  ('uuuuu -> 'uuuuu1 Prims.list) -> 'uuuuu Prims.list -> 'uuuuu1 Prims.list
val opt_map :
  ('a -> 'uuuuu Prims.list) ->
  'a FStar_Pervasives_Native.option -> 'uuuuu Prims.list
val lidents_of_term : FStar_Parser_AST.term -> FStar_Ident.lid Prims.list
val lidents_of_term' :
  FStar_Parser_AST.term' -> FStar_Ident.lident Prims.list
val lidents_of_branch :
  FStar_Parser_AST.pattern *
  FStar_Parser_AST.term FStar_Pervasives_Native.option *
  FStar_Parser_AST.term -> FStar_Ident.lid Prims.list
val lidents_of_calc_step :
  FStar_Parser_AST.calc_step -> FStar_Ident.lid Prims.list
val lidents_of_pattern :
  FStar_Parser_AST.pattern -> FStar_Ident.lid Prims.list
val lidents_of_binder : FStar_Parser_AST.binder -> FStar_Ident.lid Prims.list
val lidents_of_tycon_record :
  'uuuuu * 'uuuuu1 * 'uuuuu2 * FStar_Parser_AST.term ->
  FStar_Ident.lid Prims.list
val lidents_of_constructor_payload :
  FStar_Parser_AST.constructor_payload -> FStar_Ident.lident Prims.list
val lidents_of_tycon_variant :
  FStar_Ident.ident *
  FStar_Parser_AST.constructor_payload FStar_Pervasives_Native.option *
  FStar_Parser_AST.attributes_ -> FStar_Ident.lident Prims.list
val lidents_of_tycon :
  FStar_Parser_AST.tycon -> FStar_Ident.lident Prims.list
val lidents_of_lift : FStar_Parser_AST.lift -> FStar_Ident.lident Prims.list
val lidents_of_decl : FStar_Parser_AST.decl -> FStar_Ident.lid Prims.list
val lidents_of_effect_decl :
  FStar_Parser_AST.effect_decl -> FStar_Ident.lid Prims.list

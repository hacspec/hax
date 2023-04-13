val maybe_unthunk : FStar_Parser_AST.term -> FStar_Parser_AST.term
val min : Prims.int -> Prims.int -> Prims.int
val max : Prims.int -> Prims.int -> Prims.int
val map_rev : ('a -> 'b) -> 'a Prims.list -> 'b Prims.list
val map_if_all :
  ('a -> 'b FStar_Pervasives_Native.option) ->
  'a Prims.list -> 'b Prims.list FStar_Pervasives_Native.option
val all : ('a -> Prims.bool) -> 'a Prims.list -> Prims.bool
val all1_explicit :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool
val unfold_tuples : Prims.bool FStar_Compiler_Effect.ref
val str : Prims.string -> FStar_Pprint.document
val default_or_map :
  'uuuuu ->
  ('uuuuu1 -> 'uuuuu) -> 'uuuuu1 FStar_Pervasives_Native.option -> 'uuuuu
val prefix2 :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
val prefix2_nonempty :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
val op_Hat_Slash_Plus_Hat :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
val jump2 : FStar_Pprint.document -> FStar_Pprint.document
val infix2 :
  FStar_Pprint.document ->
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
val infix0 :
  FStar_Pprint.document ->
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
val break1 : FStar_Pprint.document
val separate_break_map :
  FStar_Pprint.document ->
  ('uuuuu -> FStar_Pprint.document) ->
  'uuuuu Prims.list -> FStar_Pprint.document
val precede_break_separate_map :
  FStar_Pprint.document ->
  FStar_Pprint.document ->
  ('uuuuu -> FStar_Pprint.document) ->
  'uuuuu Prims.list -> FStar_Pprint.document
val concat_break_map :
  ('uuuuu -> FStar_Pprint.document) ->
  'uuuuu Prims.list -> FStar_Pprint.document
val parens_with_nesting : FStar_Pprint.document -> FStar_Pprint.document
val soft_parens_with_nesting : FStar_Pprint.document -> FStar_Pprint.document
val braces_with_nesting : FStar_Pprint.document -> FStar_Pprint.document
val soft_braces_with_nesting : FStar_Pprint.document -> FStar_Pprint.document
val soft_braces_with_nesting_tight :
  FStar_Pprint.document -> FStar_Pprint.document
val brackets_with_nesting : FStar_Pprint.document -> FStar_Pprint.document
val soft_brackets_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document
val soft_begin_end_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document
val tc_arg : FStar_Pprint.document -> FStar_Pprint.document
val is_tc_binder : FStar_Parser_AST.binder -> Prims.bool
val is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool
val is_joinable_binder : FStar_Parser_AST.binder -> Prims.bool
val separate_map_last :
  FStar_Pprint.document ->
  (Prims.bool -> 'uuuuu -> FStar_Pprint.document) ->
  'uuuuu Prims.list -> FStar_Pprint.document
val separate_break_map_last :
  FStar_Pprint.document ->
  (Prims.bool -> 'uuuuu -> FStar_Pprint.document) ->
  'uuuuu Prims.list -> FStar_Pprint.document
val separate_map_or_flow :
  FStar_Pprint.document ->
  ('uuuuu -> FStar_Pprint.document) ->
  'uuuuu Prims.list -> FStar_Pprint.document
val flow_map_last :
  FStar_Pprint.document ->
  (Prims.bool -> 'uuuuu -> FStar_Pprint.document) ->
  'uuuuu Prims.list -> FStar_Pprint.document
val separate_map_or_flow_last :
  FStar_Pprint.document ->
  (Prims.bool -> 'uuuuu -> FStar_Pprint.document) ->
  'uuuuu Prims.list -> FStar_Pprint.document
val separate_or_flow :
  FStar_Pprint.document ->
  FStar_Pprint.document Prims.list -> FStar_Pprint.document
val surround_maybe_empty :
  Prims.int ->
  Prims.int ->
  FStar_Pprint.document ->
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
val soft_surround_separate_map :
  Prims.int ->
  Prims.int ->
  FStar_Pprint.document ->
  FStar_Pprint.document ->
  FStar_Pprint.document ->
  FStar_Pprint.document ->
  ('uuuuu -> FStar_Pprint.document) ->
  'uuuuu Prims.list -> FStar_Pprint.document
val soft_surround_map_or_flow :
  Prims.int ->
  Prims.int ->
  FStar_Pprint.document ->
  FStar_Pprint.document ->
  FStar_Pprint.document ->
  FStar_Pprint.document ->
  ('uuuuu -> FStar_Pprint.document) ->
  'uuuuu Prims.list -> FStar_Pprint.document
val is_unit : FStar_Parser_AST.term -> Prims.bool
val matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool
val is_tuple_constructor : FStar_Ident.lident -> Prims.bool
val is_dtuple_constructor : FStar_Ident.lident -> Prims.bool
val is_list_structure :
  FStar_Ident.lident ->
  FStar_Ident.lident -> FStar_Parser_AST.term -> Prims.bool
val is_list : FStar_Parser_AST.term -> Prims.bool
val extract_from_list :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list
val is_array : FStar_Parser_AST.term -> Prims.bool
val is_ref_set : FStar_Parser_AST.term -> Prims.bool
val extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list
val is_general_application : FStar_Parser_AST.term -> Prims.bool
val is_general_construction : FStar_Parser_AST.term -> Prims.bool
val is_general_prefix_op : FStar_Ident.ident -> Prims.bool
val head_and_args :
  FStar_Parser_AST.term ->
  FStar_Parser_AST.term *
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list
type associativity = Left | Right | NonAssoc
val uu___is_Left : associativity -> Prims.bool
val uu___is_Right : associativity -> Prims.bool
val uu___is_NonAssoc : associativity -> Prims.bool
type token =
    StartsWith of FStar_Char.char
  | Exact of Prims.string
  | UnicodeOperator
val uu___is_StartsWith : token -> Prims.bool
val __proj__StartsWith__item___0 : token -> FStar_Char.char
val uu___is_Exact : token -> Prims.bool
val __proj__Exact__item___0 : token -> Prims.string
val uu___is_UnicodeOperator : token -> Prims.bool
type associativity_level = associativity * token Prims.list
val token_to_string : token -> Prims.string
val is_non_latin_char : FStar_Char.char -> Prims.bool
val matches_token : Prims.string -> token -> Prims.bool
val matches_level : Prims.string -> 'uuuuu * token Prims.list -> Prims.bool
val opinfix4 : associativity_level
val opinfix3 : associativity_level
val opinfix2 : associativity_level
val minus_lvl : associativity_level
val opinfix1 : associativity_level
val pipe_right : associativity_level
val opinfix0d : associativity_level
val opinfix0c : associativity_level
val equal : associativity_level
val opinfix0b : associativity_level
val opinfix0a : associativity_level
val colon_equals : associativity_level
val amp : associativity_level
val colon_colon : associativity_level
val level_associativity_spec : associativity_level Prims.list
val level_table :
  ((Prims.int * Prims.int * Prims.int) * token Prims.list) Prims.list
val assign_levels :
  associativity_level Prims.list ->
  Prims.string -> Prims.int * Prims.int * Prims.int
val max_level : ('uuuuu * token Prims.list) Prims.list -> Prims.int
val levels : Prims.string -> Prims.int * Prims.int * Prims.int
val operatorInfix0ad12 : associativity_level Prims.list
val is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool
val is_operatorInfix34 : FStar_Ident.ident -> Prims.bool
val handleable_args_length : FStar_Ident.ident -> Prims.int
val handleable_op : FStar_Ident.ident -> 'uuuuu Prims.list -> Prims.bool
type annotation_style =
    Binders of (Prims.int * Prims.int * Prims.bool)
  | Arrows of (Prims.int * Prims.int)
val uu___is_Binders : annotation_style -> Prims.bool
val __proj__Binders__item___0 :
  annotation_style -> Prims.int * Prims.int * Prims.bool
val uu___is_Arrows : annotation_style -> Prims.bool
val __proj__Arrows__item___0 : annotation_style -> Prims.int * Prims.int
val all_binders_annot : FStar_Parser_AST.term -> Prims.bool
type catf =
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
val cat_with_colon :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
val comment_stack :
  (Prims.string * FStar_Compiler_Range.range) Prims.list
  FStar_Compiler_Effect.ref
type decl_meta = {
  r : FStar_Compiler_Range.range;
  has_qs : Prims.bool;
  has_attrs : Prims.bool;
}
val __proj__Mkdecl_meta__item__r : decl_meta -> FStar_Compiler_Range.range
val __proj__Mkdecl_meta__item__has_qs : decl_meta -> Prims.bool
val __proj__Mkdecl_meta__item__has_attrs : decl_meta -> Prims.bool
val dummy_meta : decl_meta
val with_comment :
  ('uuuuu -> FStar_Pprint.document) ->
  'uuuuu -> FStar_Compiler_Range.range -> FStar_Pprint.document
val with_comment_sep :
  ('uuuuu -> 'uuuuu1) ->
  'uuuuu -> FStar_Compiler_Range.range -> FStar_Pprint.document * 'uuuuu1
val place_comments_until_pos :
  Prims.int ->
  Prims.int ->
  FStar_Compiler_Range.pos ->
  decl_meta ->
  FStar_Pprint.document -> Prims.bool -> Prims.bool -> FStar_Pprint.document
val separate_map_with_comments :
  FStar_Pprint.document ->
  FStar_Pprint.document ->
  ('uuuuu -> FStar_Pprint.document) ->
  'uuuuu Prims.list -> ('uuuuu -> decl_meta) -> FStar_Pprint.document
val separate_map_with_comments_kw :
  'uuuuu ->
  'uuuuu ->
  ('uuuuu -> 'uuuuu1 -> FStar_Pprint.document) ->
  'uuuuu1 Prims.list -> ('uuuuu1 -> decl_meta) -> FStar_Pprint.document
val p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document
val p_attributes :
  Prims.bool -> FStar_Parser_AST.attributes_ -> FStar_Pprint.document
val p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document
val p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
  FStar_Pprint.document ->
  FStar_Ident.ident Prims.list -> FStar_Pprint.document
val p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document
val p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document
val p_typars : FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document
val p_typeDeclWithKw :
  FStar_Pprint.document -> FStar_Parser_AST.tycon -> FStar_Pprint.document
val p_typeDecl :
  FStar_Pprint.document ->
  FStar_Parser_AST.tycon ->
  FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document *
  (FStar_Pprint.document -> FStar_Pprint.document)
val p_typeDeclRecord : FStar_Parser_AST.tycon_record -> FStar_Pprint.document
val p_typeDeclPrefix :
  FStar_Pprint.document ->
  Prims.bool ->
  FStar_Ident.ident ->
  FStar_Parser_AST.binder Prims.list ->
  FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
  FStar_Pprint.document
val p_recordFieldDecl :
  Prims.bool ->
  FStar_Ident.ident * FStar_Parser_AST.aqual * FStar_Parser_AST.attributes_ *
  FStar_Parser_AST.term -> FStar_Pprint.document
val p_constructorBranch :
  FStar_Ident.ident *
  FStar_Parser_AST.constructor_payload FStar_Pervasives_Native.option *
  FStar_Parser_AST.attributes_ -> FStar_Pprint.document
val p_letlhs :
  FStar_Pprint.document ->
  FStar_Parser_AST.pattern * FStar_Parser_AST.term ->
  Prims.bool -> FStar_Pprint.document
val p_letbinding :
  FStar_Pprint.document ->
  FStar_Parser_AST.pattern * FStar_Parser_AST.term -> FStar_Pprint.document
val p_term_list :
  Prims.bool ->
  Prims.bool -> FStar_Parser_AST.term Prims.list -> FStar_Pprint.document
val p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document
val p_effectRedefinition :
  FStar_Ident.ident ->
  FStar_Parser_AST.binder Prims.list ->
  FStar_Parser_AST.term -> FStar_Pprint.document
val p_effectDefinition :
  FStar_Ident.ident ->
  FStar_Parser_AST.binder Prims.list ->
  FStar_Parser_AST.term ->
  FStar_Parser_AST.decl Prims.list -> FStar_Pprint.document
val p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document
val p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document
val p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document
val p_qualifiers : FStar_Parser_AST.qualifiers -> FStar_Pprint.document
val p_letqualifier : FStar_Parser_AST.let_qualifier -> FStar_Pprint.document
val p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document
val p_disjunctivePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
val p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
val p_constructorPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
val p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
val is_typ_tuple : FStar_Parser_AST.term -> Prims.bool
val p_binder : Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
val p_binder' :
  Prims.bool ->
  Prims.bool ->
  FStar_Parser_AST.binder ->
  FStar_Pprint.document *
  (FStar_Pprint.document * catf) FStar_Pervasives_Native.option
val p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
  FStar_Parser_AST.term Prims.list ->
  FStar_Pprint.document ->
  FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
val p_refinement' :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
  FStar_Parser_AST.term Prims.list ->
  FStar_Pprint.document ->
  FStar_Parser_AST.term ->
  FStar_Parser_AST.term -> FStar_Pprint.document * FStar_Pprint.document
val p_binders_list :
  Prims.bool ->
  FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list
val p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document
val p_binders_sep :
  FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document
val string_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document
val text_of_lid_or_underscore : FStar_Ident.lid -> FStar_Pprint.document
val p_qlident : FStar_Ident.lid -> FStar_Pprint.document
val p_quident : FStar_Ident.lid -> FStar_Pprint.document
val p_ident : FStar_Ident.ident -> FStar_Pprint.document
val p_lident : FStar_Ident.ident -> FStar_Pprint.document
val p_uident : FStar_Ident.ident -> FStar_Pprint.document
val p_tvar : FStar_Ident.ident -> FStar_Pprint.document
val paren_if : Prims.bool -> FStar_Pprint.document -> FStar_Pprint.document
val inline_comment_or_above :
  FStar_Pprint.document ->
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
val p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document
val p_term_sep :
  Prims.bool ->
  Prims.bool ->
  FStar_Parser_AST.term -> FStar_Pprint.document * FStar_Pprint.document
val p_noSeqTerm :
  Prims.bool ->
  Prims.bool ->
  FStar_Parser_AST.term -> FStar_Pprint.document * FStar_Pprint.document
val p_noSeqTermAndComment :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document
val p_noSeqTerm' :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document
val p_dec_wf :
  Prims.bool ->
  Prims.bool ->
  FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
val p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document
val p_attrs_opt :
  Prims.bool ->
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
  FStar_Pprint.document
val p_typ :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.knd -> FStar_Pprint.document
val p_typ_sep :
  Prims.bool ->
  Prims.bool ->
  FStar_Parser_AST.term -> FStar_Pprint.document * FStar_Pprint.document
val p_typ' :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document
val p_typ_top :
  annotation_style ->
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document
val p_typ_top' :
  annotation_style ->
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document
val sig_as_binders_if_possible :
  FStar_Parser_AST.term -> Prims.bool -> FStar_Pprint.document
val collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document * Prims.bool * Prims.bool)
  Prims.list -> FStar_Pprint.document Prims.list
val pats_as_binders_if_possible :
  FStar_Parser_AST.pattern Prims.list ->
  FStar_Pprint.document Prims.list * annotation_style
val p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document
val p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document
val p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document
val p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document
val p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document
val p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document
val p_patternBranch :
  Prims.bool ->
  FStar_Parser_AST.pattern *
  FStar_Parser_AST.term FStar_Pervasives_Native.option *
  FStar_Parser_AST.term -> FStar_Pprint.document
val p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document
val p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document
val format_sig :
  annotation_style ->
  FStar_Pprint.document Prims.list ->
  FStar_Pprint.document -> Prims.bool -> Prims.bool -> FStar_Pprint.document
val p_tmArrow :
  annotation_style ->
  Prims.bool ->
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
  FStar_Parser_AST.term -> FStar_Pprint.document
val p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
  FStar_Parser_AST.term ->
  FStar_Pprint.document Prims.list * FStar_Pprint.document
val collapse_binders :
  annotation_style ->
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
  FStar_Parser_AST.term ->
  FStar_Pprint.document Prims.list * FStar_Pprint.document
val p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document
val p_tmDisjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list Prims.list
val p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list
val p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document
val p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document
val paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document
val p_tmEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
  FStar_Parser_AST.term -> FStar_Pprint.document
val p_tmEqWith' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
  Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document
val p_tmNoEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
  FStar_Parser_AST.term -> FStar_Pprint.document
val p_tmNoEqWith' :
  Prims.bool ->
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
  Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document
val p_tmEqNoRefinement : FStar_Parser_AST.term -> FStar_Pprint.document
val p_tmEq : FStar_Parser_AST.term -> FStar_Pprint.document
val p_tmNoEq : FStar_Parser_AST.term -> FStar_Pprint.document
val p_tmRefinement : FStar_Parser_AST.term -> FStar_Pprint.document
val p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document
val p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document
val p_simpleDef :
  Prims.bool ->
  FStar_Ident.lid * FStar_Parser_AST.term -> FStar_Pprint.document
val p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document
val p_argTerm :
  FStar_Parser_AST.term * FStar_Parser_AST.imp -> FStar_Pprint.document
val p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
  FStar_Parser_AST.term -> FStar_Pprint.document
val p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document
val p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document
val p_atomicTermNotQUident : FStar_Parser_AST.term -> FStar_Pprint.document
val p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document
val p_constant : FStar_Const.sconst -> FStar_Pprint.document
val p_universe : FStar_Parser_AST.term -> FStar_Pprint.document
val p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document
val p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document
val term_to_document : FStar_Parser_AST.term -> FStar_Pprint.document
val signature_to_document : FStar_Parser_AST.decl -> FStar_Pprint.document
val decl_to_document : FStar_Parser_AST.decl -> FStar_Pprint.document
val pat_to_document : FStar_Parser_AST.pattern -> FStar_Pprint.document
val binder_to_document : FStar_Parser_AST.binder -> FStar_Pprint.document
val modul_to_document : FStar_Parser_AST.modul -> FStar_Pprint.document
val comments_to_document :
  (Prims.string * FStar_Compiler_Range.range) Prims.list ->
  FStar_Pprint.document
val extract_decl_range : FStar_Parser_AST.decl -> decl_meta
val decls_with_comments_to_document :
  FStar_Parser_AST.decl Prims.list ->
  (Prims.string * FStar_Compiler_Range.range) Prims.list ->
  FStar_Pprint.document *
  (Prims.string * FStar_Compiler_Range.range) Prims.list
val modul_with_comments_to_document :
  FStar_Parser_AST.modul ->
  (Prims.string * FStar_Compiler_Range.range) Prims.list ->
  FStar_Pprint.document *
  (Prims.string * FStar_Compiler_Range.range) Prims.list
val decl_with_comments_to_document :
  FStar_Parser_AST.decl ->
  (Prims.string * FStar_Compiler_Range.range) Prims.list ->
  FStar_Pprint.document *
  (Prims.string * FStar_Compiler_Range.range) Prims.list

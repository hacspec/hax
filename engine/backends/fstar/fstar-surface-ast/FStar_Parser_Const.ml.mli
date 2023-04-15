val p2l : FStar_Ident.path -> FStar_Ident.lident
val pconst : Prims.string -> FStar_Ident.lident
val psconst : Prims.string -> FStar_Ident.lident
val psnconst : Prims.string -> FStar_Ident.lident
val prims_lid : FStar_Ident.lident
val pervasives_native_lid : FStar_Ident.lident
val pervasives_lid : FStar_Ident.lident
val fstar_ns_lid : FStar_Ident.lident
val bool_lid : FStar_Ident.lident
val unit_lid : FStar_Ident.lident
val squash_lid : FStar_Ident.lident
val auto_squash_lid : FStar_Ident.lident
val string_lid : FStar_Ident.lident
val bytes_lid : FStar_Ident.lident
val int_lid : FStar_Ident.lident
val exn_lid : FStar_Ident.lident
val list_lid : FStar_Ident.lident
val immutable_array_t_lid : FStar_Ident.lident
val immutable_array_of_list_lid : FStar_Ident.lident
val immutable_array_length_lid : FStar_Ident.lident
val immutable_array_index_lid : FStar_Ident.lident
val eqtype_lid : FStar_Ident.lident
val option_lid : FStar_Ident.lident
val either_lid : FStar_Ident.lident
val pattern_lid : FStar_Ident.lident
val lex_t_lid : FStar_Ident.lident
val precedes_lid : FStar_Ident.lident
val smtpat_lid : FStar_Ident.lident
val smtpatOr_lid : FStar_Ident.lident
val monadic_lid : FStar_Ident.lident
val spinoff_lid : FStar_Ident.lident
val inl_lid : FStar_Ident.lident
val inr_lid : FStar_Ident.lident
val int8_lid : FStar_Ident.lident
val uint8_lid : FStar_Ident.lident
val int16_lid : FStar_Ident.lident
val uint16_lid : FStar_Ident.lident
val int32_lid : FStar_Ident.lident
val uint32_lid : FStar_Ident.lident
val int64_lid : FStar_Ident.lident
val uint64_lid : FStar_Ident.lident
val salloc_lid : FStar_Ident.lident
val swrite_lid : FStar_Ident.lident
val sread_lid : FStar_Ident.lident
val max_lid : FStar_Ident.lident
val real_lid : FStar_Ident.lident
val float_lid : FStar_Ident.lident
val char_lid : FStar_Ident.lident
val heap_lid : FStar_Ident.lident
val logical_lid : FStar_Ident.lident
val smt_theory_symbol_attr_lid : FStar_Ident.lident
val true_lid : FStar_Ident.lident
val false_lid : FStar_Ident.lident
val and_lid : FStar_Ident.lident
val or_lid : FStar_Ident.lident
val not_lid : FStar_Ident.lident
val imp_lid : FStar_Ident.lident
val iff_lid : FStar_Ident.lident
val ite_lid : FStar_Ident.lident
val exists_lid : FStar_Ident.lident
val forall_lid : FStar_Ident.lident
val haseq_lid : FStar_Ident.lident
val b2t_lid : FStar_Ident.lident
val admit_lid : FStar_Ident.lident
val magic_lid : FStar_Ident.lident
val has_type_lid : FStar_Ident.lident
val c_true_lid : FStar_Ident.lident
val empty_type_lid : FStar_Ident.lident
val c_and_lid : FStar_Ident.lident
val c_or_lid : FStar_Ident.lident
val dtuple2_lid : FStar_Ident.lident
val eq2_lid : FStar_Ident.lident
val eq3_lid : FStar_Ident.lident
val c_eq2_lid : FStar_Ident.lident
val cons_lid : FStar_Ident.lident
val nil_lid : FStar_Ident.lident
val some_lid : FStar_Ident.lident
val none_lid : FStar_Ident.lident
val assume_lid : FStar_Ident.lident
val assert_lid : FStar_Ident.lident
val pure_wp_lid : FStar_Ident.lident
val pure_wp_monotonic_lid : FStar_Ident.lident
val pure_wp_monotonic0_lid : FStar_Ident.lident
val trivial_pure_post_lid : FStar_Ident.lident
val pure_assert_wp_lid : FStar_Ident.lident
val pure_assume_wp_lid : FStar_Ident.lident
val assert_norm_lid : FStar_Ident.lident
val list_append_lid : FStar_Ident.lident
val list_tot_append_lid : FStar_Ident.lident
val id_lid : FStar_Ident.lident
val c2l : Prims.string -> FStar_Ident.lident
val char_u32_of_char : FStar_Ident.lident
val s2l : Prims.string -> FStar_Ident.lident
val string_list_of_string_lid : FStar_Ident.lident
val string_string_of_list_lid : FStar_Ident.lident
val string_make_lid : FStar_Ident.lident
val string_split_lid : FStar_Ident.lident
val string_concat_lid : FStar_Ident.lident
val string_compare_lid : FStar_Ident.lident
val string_lowercase_lid : FStar_Ident.lident
val string_uppercase_lid : FStar_Ident.lident
val string_index_lid : FStar_Ident.lident
val string_index_of_lid : FStar_Ident.lident
val string_sub_lid : FStar_Ident.lident
val prims_strcat_lid : FStar_Ident.lident
val prims_op_Hat_lid : FStar_Ident.lident
val let_in_typ : FStar_Ident.lident
val string_of_int_lid : FStar_Ident.lident
val string_of_bool_lid : FStar_Ident.lident
val string_compare : FStar_Ident.lident
val order_lid : FStar_Ident.lident
val vconfig_lid : FStar_Ident.lident
val mkvconfig_lid : FStar_Ident.lident
val op_Eq : FStar_Ident.lident
val op_notEq : FStar_Ident.lident
val op_LT : FStar_Ident.lident
val op_LTE : FStar_Ident.lident
val op_GT : FStar_Ident.lident
val op_GTE : FStar_Ident.lident
val op_Subtraction : FStar_Ident.lident
val op_Minus : FStar_Ident.lident
val op_Addition : FStar_Ident.lident
val op_Multiply : FStar_Ident.lident
val op_Division : FStar_Ident.lident
val op_Modulus : FStar_Ident.lident
val op_And : FStar_Ident.lident
val op_Or : FStar_Ident.lident
val op_Negation : FStar_Ident.lident
val real_const : Prims.string -> FStar_Ident.lident
val real_op_LT : FStar_Ident.lident
val real_op_LTE : FStar_Ident.lident
val real_op_GT : FStar_Ident.lident
val real_op_GTE : FStar_Ident.lident
val real_op_Subtraction : FStar_Ident.lident
val real_op_Addition : FStar_Ident.lident
val real_op_Multiply : FStar_Ident.lident
val real_op_Division : FStar_Ident.lident
val real_of_int : FStar_Ident.lident
val bvconst : Prims.string -> FStar_Ident.lident
val bv_t_lid : FStar_Ident.lident
val nat_to_bv_lid : FStar_Ident.lident
val bv_to_nat_lid : FStar_Ident.lident
val bv_and_lid : FStar_Ident.lident
val bv_xor_lid : FStar_Ident.lident
val bv_or_lid : FStar_Ident.lident
val bv_add_lid : FStar_Ident.lident
val bv_sub_lid : FStar_Ident.lident
val bv_shift_left_lid : FStar_Ident.lident
val bv_shift_right_lid : FStar_Ident.lident
val bv_udiv_lid : FStar_Ident.lident
val bv_mod_lid : FStar_Ident.lident
val bv_mul_lid : FStar_Ident.lident
val bv_ult_lid : FStar_Ident.lident
val bv_uext_lid : FStar_Ident.lident
val array_lid : FStar_Ident.lident
val array_of_list_lid : FStar_Ident.lident
val st_lid : FStar_Ident.lident
val write_lid : FStar_Ident.lident
val read_lid : FStar_Ident.lident
val alloc_lid : FStar_Ident.lident
val op_ColonEq : FStar_Ident.lident
val ref_lid : FStar_Ident.lident
val heap_addr_of_lid : FStar_Ident.lident
val set_empty : FStar_Ident.lident
val set_singleton : FStar_Ident.lident
val set_union : FStar_Ident.lident
val fstar_hyperheap_lid : FStar_Ident.lident
val rref_lid : FStar_Ident.lident
val erased_lid : FStar_Ident.lident
val effect_PURE_lid : FStar_Ident.lident
val effect_Pure_lid : FStar_Ident.lident
val effect_Tot_lid : FStar_Ident.lident
val effect_Lemma_lid : FStar_Ident.lident
val effect_GTot_lid : FStar_Ident.lident
val effect_GHOST_lid : FStar_Ident.lident
val effect_Ghost_lid : FStar_Ident.lident
val effect_DIV_lid : FStar_Ident.lident
val effect_Div_lid : FStar_Ident.lident
val effect_Dv_lid : FStar_Ident.lident
val compiler_effect_lid : FStar_Ident.lident
val compiler_effect_ALL_lid : FStar_Ident.lident
val compiler_effect_ML_lid : FStar_Ident.lident
val compiler_effect_failwith_lid : FStar_Ident.lident
val compiler_effect_try_with_lid : FStar_Ident.lident
val all_lid : FStar_Ident.lident
val all_ALL_lid : FStar_Ident.lident
val all_ML_lid : FStar_Ident.lident
val all_failwith_lid : FStar_Ident.lident
val all_try_with_lid : FStar_Ident.lident
val effect_ALL_lid : Prims.unit -> FStar_Ident.lident
val effect_ML_lid : Prims.unit -> FStar_Ident.lident
val failwith_lid : Prims.unit -> FStar_Ident.lident
val try_with_lid : Prims.unit -> FStar_Ident.lident
val as_requires : FStar_Ident.lident
val as_ensures : FStar_Ident.lident
val decreases_lid : FStar_Ident.lident
val inspect : FStar_Ident.lident
val pack : FStar_Ident.lident
val binder_to_term : FStar_Ident.lident
val reveal : FStar_Ident.lident
val hide : FStar_Ident.lident
val term_lid : FStar_Ident.lident
val term_view_lid : FStar_Ident.lident
val decls_lid : FStar_Ident.lident
val ctx_uvar_and_subst_lid : FStar_Ident.lident
val universe_uvar_lid : FStar_Ident.lident
val range_lid : FStar_Ident.lident
val range_of_lid : FStar_Ident.lident
val labeled_lid : FStar_Ident.lident
val range_0 : FStar_Ident.lident
val guard_free : FStar_Ident.lident
val inversion_lid : FStar_Ident.lident
val normalize : FStar_Ident.lident
val normalize_term : FStar_Ident.lident
val norm : FStar_Ident.lident
val steps_simpl : FStar_Ident.lident
val steps_weak : FStar_Ident.lident
val steps_hnf : FStar_Ident.lident
val steps_primops : FStar_Ident.lident
val steps_zeta : FStar_Ident.lident
val steps_zeta_full : FStar_Ident.lident
val steps_iota : FStar_Ident.lident
val steps_delta : FStar_Ident.lident
val steps_reify : FStar_Ident.lident
val steps_unfoldonly : FStar_Ident.lident
val steps_unfoldfully : FStar_Ident.lident
val steps_unfoldattr : FStar_Ident.lident
val steps_unfoldqual : FStar_Ident.lident
val steps_unfoldnamespace : FStar_Ident.lident
val steps_unascribe : FStar_Ident.lident
val steps_nbe : FStar_Ident.lident
val steps_unmeta : FStar_Ident.lident
val deprecated_attr : FStar_Ident.lident
val warn_on_use_attr : FStar_Ident.lident
val inline_let_attr : FStar_Ident.lident
val rename_let_attr : FStar_Ident.lident
val plugin_attr : FStar_Ident.lident
val tcnorm_attr : FStar_Ident.lident
val dm4f_bind_range_attr : FStar_Ident.lident
val must_erase_for_extraction_attr : FStar_Ident.lident
val strict_on_arguments_attr : FStar_Ident.lident
val resolve_implicits_attr_string : Prims.string
val override_resolve_implicits_handler_lid : FStar_Ident.lident
val handle_smt_goals_attr : FStar_Ident.lident
val handle_smt_goals_attr_string : Prims.string
val erasable_attr : FStar_Ident.lident
val comment_attr : FStar_Ident.lident
val fail_attr : FStar_Ident.lident
val fail_lax_attr : FStar_Ident.lident
val tcdecltime_attr : FStar_Ident.lident
val noextract_to_attr : FStar_Ident.lident
val unifier_hint_injective_lid : FStar_Ident.lident
val normalize_for_extraction_lid : FStar_Ident.lident
val postprocess_with : FStar_Ident.lident
val preprocess_with : FStar_Ident.lident
val postprocess_extr_with : FStar_Ident.lident
val check_with_lid : FStar_Ident.lident
val commute_nested_matches_lid : FStar_Ident.lident
val remove_unused_type_parameters_lid : FStar_Ident.lident
val ite_soundness_by_attr : FStar_Ident.lident
val default_effect_attr : FStar_Ident.lident
val top_level_effect_attr : FStar_Ident.lident
val effect_parameter_attr : FStar_Ident.lident
val bind_has_range_args_attr : FStar_Ident.lident
val primitive_extraction_attr : FStar_Ident.lident
val binder_strictly_positive_attr : FStar_Ident.lident
val no_auto_projectors_attr : FStar_Ident.lident
val no_subtping_attr_lid : FStar_Ident.lident
val attr_substitute_lid : FStar_Ident.lident
val well_founded_relation_lid : FStar_Ident.lident
val gen_reset : (Prims.unit -> Prims.int) * (Prims.unit -> Prims.unit)
val next_id : Prims.unit -> Prims.int
val sli : FStar_Ident.lident -> Prims.string
val const_to_string : FStar_Const.sconst -> Prims.string
val mk_tuple_lid :
  Prims.int -> FStar_Compiler_Range.range -> FStar_Ident.lident
val lid_tuple2 : FStar_Ident.lident
val lid_tuple3 : FStar_Ident.lident
val is_tuple_constructor_string : Prims.string -> Prims.bool
val is_tuple_constructor_id : FStar_Ident.ident -> Prims.bool
val is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool
val mk_tuple_data_lid :
  Prims.int -> FStar_Compiler_Range.range -> FStar_Ident.lident
val lid_Mktuple2 : FStar_Ident.lident
val lid_Mktuple3 : FStar_Ident.lident
val is_tuple_datacon_string : Prims.string -> Prims.bool
val is_tuple_datacon_id : FStar_Ident.ident -> Prims.bool
val is_tuple_datacon_lid : FStar_Ident.lident -> Prims.bool
val is_tuple_data_lid : FStar_Ident.lident -> Prims.int -> Prims.bool
val is_tuple_data_lid' : FStar_Ident.lident -> Prims.bool
val mod_prefix_dtuple : Prims.int -> Prims.string -> FStar_Ident.lident
val mk_dtuple_lid :
  Prims.int -> FStar_Compiler_Range.range -> FStar_Ident.lident
val is_dtuple_constructor_string : Prims.string -> Prims.bool
val is_dtuple_constructor_lid : FStar_Ident.lident -> Prims.bool
val mk_dtuple_data_lid :
  Prims.int -> FStar_Compiler_Range.range -> FStar_Ident.lident
val is_dtuple_datacon_string : Prims.string -> Prims.bool
val is_dtuple_data_lid : FStar_Ident.lident -> Prims.int -> Prims.bool
val is_dtuple_data_lid' : FStar_Ident.lident -> Prims.bool
val is_name : FStar_Ident.lident -> Prims.bool
val fstar_tactics_lid' : Prims.string Prims.list -> FStar_Ident.lid
val fstar_tactics_lid : Prims.string -> FStar_Ident.lid
val tac_lid : FStar_Ident.lid
val tactic_lid : FStar_Ident.lid
val mk_class_lid : FStar_Ident.lid
val tcresolve_lid : FStar_Ident.lid
val tcclass_lid : FStar_Ident.lid
val tcinstance_lid : FStar_Ident.lid
val no_method_lid : FStar_Ident.lid
val effect_TAC_lid : FStar_Ident.lid
val effect_Tac_lid : FStar_Ident.lid
val by_tactic_lid : FStar_Ident.lid
val rewrite_by_tactic_lid : FStar_Ident.lid
val synth_lid : FStar_Ident.lid
val assert_by_tactic_lid : FStar_Ident.lid
val fstar_syntax_syntax_term : FStar_Ident.lident
val binder_lid : FStar_Ident.lident
val binders_lid : FStar_Ident.lident
val bv_lid : FStar_Ident.lident
val fv_lid : FStar_Ident.lident
val norm_step_lid : FStar_Ident.lident
val calc_lid : Prims.string -> FStar_Ident.lid
val calc_init_lid : FStar_Ident.lid
val calc_step_lid : FStar_Ident.lid
val calc_finish_lid : FStar_Ident.lid
val calc_push_impl_lid : FStar_Ident.lid
val classical_sugar_lid : Prims.string -> FStar_Ident.lid
val forall_intro_lid : FStar_Ident.lid
val exists_intro_lid : FStar_Ident.lid
val implies_intro_lid : FStar_Ident.lid
val or_intro_left_lid : FStar_Ident.lid
val or_intro_right_lid : FStar_Ident.lid
val and_intro_lid : FStar_Ident.lid
val forall_elim_lid : FStar_Ident.lid
val exists_elim_lid : FStar_Ident.lid
val implies_elim_lid : FStar_Ident.lid
val or_elim_lid : FStar_Ident.lid
val and_elim_lid : FStar_Ident.lid
val match_returns_def_name : Prims.string
val steel_memory_inv_lid : FStar_Ident.lident
val steel_new_invariant_lid : FStar_Ident.lident
val steel_st_new_invariant_lid : FStar_Ident.lident
val steel_with_invariant_g_lid : FStar_Ident.lident
val steel_st_with_invariant_g_lid : FStar_Ident.lident
val steel_with_invariant_lid : FStar_Ident.lident
val steel_st_with_invariant_lid : FStar_Ident.lident
val fext_lid : Prims.string -> FStar_Ident.lident
val fext_on_domain_lid : FStar_Ident.lident
val fext_on_dom_lid : FStar_Ident.lident
val fext_on_domain_g_lid : FStar_Ident.lident
val fext_on_dom_g_lid : FStar_Ident.lident
val sealed_lid : FStar_Ident.lident
val seal_lid : FStar_Ident.lident
val unseal_lid : FStar_Ident.lident

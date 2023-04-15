type debug_level_t = Low | Medium | High | Extreme | Other of Prims.string
val uu___is_Low : debug_level_t -> Prims.bool
val uu___is_Medium : debug_level_t -> Prims.bool
val uu___is_High : debug_level_t -> Prims.bool
val uu___is_Extreme : debug_level_t -> Prims.bool
val uu___is_Other : debug_level_t -> Prims.bool
val __proj__Other__item___0 : debug_level_t -> Prims.string
type option_val =
    Bool of Prims.bool
  | String of Prims.string
  | Path of Prims.string
  | Int of Prims.int
  | List of option_val Prims.list
  | Unset
val uu___is_Bool : option_val -> Prims.bool
val __proj__Bool__item___0 : option_val -> Prims.bool
val uu___is_String : option_val -> Prims.bool
val __proj__String__item___0 : option_val -> Prims.string
val uu___is_Path : option_val -> Prims.bool
val __proj__Path__item___0 : option_val -> Prims.string
val uu___is_Int : option_val -> Prims.bool
val __proj__Int__item___0 : option_val -> Prims.int
val uu___is_List : option_val -> Prims.bool
val __proj__List__item___0 : option_val -> option_val Prims.list
val uu___is_Unset : option_val -> Prims.bool
type optionstate = option_val FStar_Compiler_Util.smap
type opt_type =
    Const of option_val
  | IntStr of Prims.string
  | BoolStr
  | PathStr of Prims.string
  | SimpleStr of Prims.string
  | EnumStr of Prims.string Prims.list
  | OpenEnumStr of (Prims.string Prims.list * Prims.string)
  | PostProcessed of ((option_val -> option_val) * opt_type)
  | Accumulated of opt_type
  | ReverseAccumulated of opt_type
  | WithSideEffect of ((Prims.unit -> Prims.unit) * opt_type)
val uu___is_Const : opt_type -> Prims.bool
val __proj__Const__item___0 : opt_type -> option_val
val uu___is_IntStr : opt_type -> Prims.bool
val __proj__IntStr__item___0 : opt_type -> Prims.string
val uu___is_BoolStr : opt_type -> Prims.bool
val uu___is_PathStr : opt_type -> Prims.bool
val __proj__PathStr__item___0 : opt_type -> Prims.string
val uu___is_SimpleStr : opt_type -> Prims.bool
val __proj__SimpleStr__item___0 : opt_type -> Prims.string
val uu___is_EnumStr : opt_type -> Prims.bool
val __proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list
val uu___is_OpenEnumStr : opt_type -> Prims.bool
val __proj__OpenEnumStr__item___0 :
  opt_type -> Prims.string Prims.list * Prims.string
val uu___is_PostProcessed : opt_type -> Prims.bool
val __proj__PostProcessed__item___0 :
  opt_type -> (option_val -> option_val) * opt_type
val uu___is_Accumulated : opt_type -> Prims.bool
val __proj__Accumulated__item___0 : opt_type -> opt_type
val uu___is_ReverseAccumulated : opt_type -> Prims.bool
val __proj__ReverseAccumulated__item___0 : opt_type -> opt_type
val uu___is_WithSideEffect : opt_type -> Prims.bool
val __proj__WithSideEffect__item___0 :
  opt_type -> (Prims.unit -> Prims.unit) * opt_type
val debug_embedding : Prims.bool FStar_Compiler_Effect.ref
val eager_embedding : Prims.bool FStar_Compiler_Effect.ref
val __unit_tests__ : Prims.bool FStar_Compiler_Effect.ref
val __unit_tests : Prims.unit -> Prims.bool
val __set_unit_tests : Prims.unit -> Prims.unit
val __clear_unit_tests : Prims.unit -> Prims.unit
val as_bool : option_val -> Prims.bool
val as_int : option_val -> Prims.int
val as_string : option_val -> Prims.string
val as_list' : option_val -> option_val Prims.list
val as_list : (option_val -> 'uuuuu) -> option_val -> 'uuuuu Prims.list
val as_option :
  (option_val -> 'uuuuu) ->
  option_val -> 'uuuuu FStar_Pervasives_Native.option
val as_comma_string_list : option_val -> Prims.string Prims.list
val copy_optionstate :
  'uuuuu FStar_Compiler_Util.smap -> 'uuuuu FStar_Compiler_Util.smap
val fstar_options :
  optionstate Prims.list Prims.list FStar_Compiler_Effect.ref
val internal_peek : Prims.unit -> optionstate
val peek : Prims.unit -> optionstate
val pop : Prims.unit -> Prims.unit
val push : Prims.unit -> Prims.unit
val internal_pop : Prims.unit -> Prims.bool
val internal_push : Prims.unit -> Prims.unit
val set : optionstate -> Prims.unit
val snapshot : Prims.unit -> Prims.int * Prims.unit
val rollback : Prims.int FStar_Pervasives_Native.option -> Prims.unit
val set_option : Prims.string -> option_val -> Prims.unit
val set_option' : Prims.string * option_val -> Prims.unit
val set_admit_smt_queries : Prims.bool -> Prims.unit
val defaults : (Prims.string * option_val) Prims.list
val init : Prims.unit -> Prims.unit
val clear : Prims.unit -> Prims.unit
val _run : Prims.unit
val get_option : Prims.string -> option_val
val set_verification_options : optionstate -> Prims.unit
val lookup_opt : Prims.string -> (option_val -> 'uuuuu) -> 'uuuuu
val get_abort_on : Prims.unit -> Prims.int
val get_admit_smt_queries : Prims.unit -> Prims.bool
val get_admit_except :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option
val get_compat_pre_core :
  Prims.unit -> Prims.int FStar_Pervasives_Native.option
val get_compat_pre_typed_indexed_effects : Prims.unit -> Prims.bool
val get_disallow_unification_guards : Prims.unit -> Prims.bool
val get_already_cached :
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option
val get_cache_checked_modules : Prims.unit -> Prims.bool
val get_cache_dir : Prims.unit -> Prims.string FStar_Pervasives_Native.option
val get_cache_off : Prims.unit -> Prims.bool
val get_print_cache_version : Prims.unit -> Prims.bool
val get_cmi : Prims.unit -> Prims.bool
val get_codegen : Prims.unit -> Prims.string FStar_Pervasives_Native.option
val get_codegen_lib : Prims.unit -> Prims.string Prims.list
val get_debug : Prims.unit -> Prims.string Prims.list
val get_debug_level : Prims.unit -> Prims.string Prims.list
val get_defensive : Prims.unit -> Prims.string
val get_dep : Prims.unit -> Prims.string FStar_Pervasives_Native.option
val get_detail_errors : Prims.unit -> Prims.bool
val get_detail_hint_replay : Prims.unit -> Prims.bool
val get_dump_module : Prims.unit -> Prims.string Prims.list
val get_eager_subtyping : Prims.unit -> Prims.bool
val get_error_contexts : Prims.unit -> Prims.bool
val get_expose_interfaces : Prims.unit -> Prims.bool
val get_extract :
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option
val get_extract_module : Prims.unit -> Prims.string Prims.list
val get_extract_namespace : Prims.unit -> Prims.string Prims.list
val get_force : Prims.unit -> Prims.bool
val get_hide_uvar_nums : Prims.unit -> Prims.bool
val get_hint_info : Prims.unit -> Prims.bool
val get_hint_dir : Prims.unit -> Prims.string FStar_Pervasives_Native.option
val get_hint_file : Prims.unit -> Prims.string FStar_Pervasives_Native.option
val get_in : Prims.unit -> Prims.bool
val get_ide : Prims.unit -> Prims.bool
val get_ide_id_info_off : Prims.unit -> Prims.bool
val get_lsp : Prims.unit -> Prims.bool
val get_include : Prims.unit -> Prims.string Prims.list
val get_print : Prims.unit -> Prims.bool
val get_print_in_place : Prims.unit -> Prims.bool
val get_initial_fuel : Prims.unit -> Prims.int
val get_initial_ifuel : Prims.unit -> Prims.int
val get_keep_query_captions : Prims.unit -> Prims.bool
val get_lax : Prims.unit -> Prims.bool
val get_load : Prims.unit -> Prims.string Prims.list
val get_load_cmxs : Prims.unit -> Prims.string Prims.list
val get_log_queries : Prims.unit -> Prims.bool
val get_log_types : Prims.unit -> Prims.bool
val get_max_fuel : Prims.unit -> Prims.int
val get_max_ifuel : Prims.unit -> Prims.int
val get_MLish : Prims.unit -> Prims.bool
val get_no_default_includes : Prims.unit -> Prims.bool
val get_no_extract : Prims.unit -> Prims.string Prims.list
val get_no_location_info : Prims.unit -> Prims.bool
val get_no_plugins : Prims.unit -> Prims.bool
val get_no_smt : Prims.unit -> Prims.bool
val get_normalize_pure_terms_for_extraction : Prims.unit -> Prims.bool
val get_odir : Prims.unit -> Prims.string FStar_Pervasives_Native.option
val get_ugly : Prims.unit -> Prims.bool
val get_prims : Prims.unit -> Prims.string FStar_Pervasives_Native.option
val get_print_bound_var_types : Prims.unit -> Prims.bool
val get_print_effect_args : Prims.unit -> Prims.bool
val get_print_expected_failures : Prims.unit -> Prims.bool
val get_print_full_names : Prims.unit -> Prims.bool
val get_print_implicits : Prims.unit -> Prims.bool
val get_print_universes : Prims.unit -> Prims.bool
val get_print_z3_statistics : Prims.unit -> Prims.bool
val get_prn : Prims.unit -> Prims.bool
val get_quake_lo : Prims.unit -> Prims.int
val get_quake_hi : Prims.unit -> Prims.int
val get_quake_keep : Prims.unit -> Prims.bool
val get_query_stats : Prims.unit -> Prims.bool
val get_record_hints : Prims.unit -> Prims.bool
val get_record_options : Prims.unit -> Prims.bool
val get_retry : Prims.unit -> Prims.bool
val get_reuse_hint_for :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option
val get_report_assumes :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option
val get_silent : Prims.unit -> Prims.bool
val get_smt : Prims.unit -> Prims.string FStar_Pervasives_Native.option
val get_smtencoding_elim_box : Prims.unit -> Prims.bool
val get_smtencoding_nl_arith_repr : Prims.unit -> Prims.string
val get_smtencoding_l_arith_repr : Prims.unit -> Prims.string
val get_smtencoding_valid_intro : Prims.unit -> Prims.bool
val get_smtencoding_valid_elim : Prims.unit -> Prims.bool
val get_split_queries : Prims.unit -> Prims.bool
val get_tactic_raw_binders : Prims.unit -> Prims.bool
val get_tactics_failhard : Prims.unit -> Prims.bool
val get_tactics_info : Prims.unit -> Prims.bool
val get_tactic_trace : Prims.unit -> Prims.bool
val get_tactic_trace_d : Prims.unit -> Prims.int
val get_tactics_nbe : Prims.unit -> Prims.bool
val get_tcnorm : Prims.unit -> Prims.bool
val get_timing : Prims.unit -> Prims.bool
val get_trace_error : Prims.unit -> Prims.bool
val get_unthrottle_inductives : Prims.unit -> Prims.bool
val get_unsafe_tactic_exec : Prims.unit -> Prims.bool
val get_use_eq_at_higher_order : Prims.unit -> Prims.bool
val get_use_hints : Prims.unit -> Prims.bool
val get_use_hint_hashes : Prims.unit -> Prims.bool
val get_use_native_tactics :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option
val get_no_tactics : Prims.unit -> Prims.bool
val get_using_facts_from :
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option
val get_verify_module : Prims.unit -> Prims.string Prims.list
val get_version : Prims.unit -> Prims.bool
val get_warn_default_effects : Prims.unit -> Prims.bool
val get_z3cliopt : Prims.unit -> Prims.string Prims.list
val get_z3smtopt : Prims.unit -> Prims.string Prims.list
val get_z3refresh : Prims.unit -> Prims.bool
val get_z3rlimit : Prims.unit -> Prims.int
val get_z3rlimit_factor : Prims.unit -> Prims.int
val get_z3seed : Prims.unit -> Prims.int
val get_no_positivity : Prims.unit -> Prims.bool
val get_warn_error : Prims.unit -> Prims.string Prims.list
val get_use_nbe : Prims.unit -> Prims.bool
val get_use_nbe_for_extraction : Prims.unit -> Prims.bool
val get_trivial_pre_for_unannotated_effectful_fns : Prims.unit -> Prims.bool
val get_profile :
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option
val get_profile_group_by_decl : Prims.unit -> Prims.bool
val get_profile_component :
  Prims.unit -> Prims.string Prims.list FStar_Pervasives_Native.option
val dlevel : Prims.string -> debug_level_t
val one_debug_level_geq : debug_level_t -> debug_level_t -> Prims.bool
val debug_level_geq : debug_level_t -> Prims.bool
val universe_include_path_base_dirs : Prims.string Prims.list
val _version : Prims.string FStar_Compiler_Effect.ref
val _platform : Prims.string FStar_Compiler_Effect.ref
val _compiler : Prims.string FStar_Compiler_Effect.ref
val _date : Prims.string FStar_Compiler_Effect.ref
val _commit : Prims.string FStar_Compiler_Effect.ref
val display_version : Prims.unit -> Prims.unit
val display_usage_aux :
  ('uuuuu * Prims.string * 'uuuuu1 FStar_Getopt.opt_variant * Prims.string)
  Prims.list -> Prims.unit
val mk_spec :
  FStar_BaseTypes.char * Prims.string * option_val FStar_Getopt.opt_variant *
  Prims.string -> FStar_Getopt.opt
val accumulated_option : Prims.string -> option_val -> option_val
val reverse_accumulated_option : Prims.string -> option_val -> option_val
val accumulate_string :
  Prims.string -> ('uuuuu -> Prims.string) -> 'uuuuu -> Prims.unit
val add_extract_module : Prims.string -> Prims.unit
val add_extract_namespace : Prims.string -> Prims.unit
val add_verify_module : Prims.string -> Prims.unit
exception InvalidArgument of Prims.string
val uu___is_InvalidArgument : Prims.exn -> Prims.bool
val __proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string
val parse_opt_val : Prims.string -> opt_type -> Prims.string -> option_val
val desc_of_opt_type :
  opt_type -> Prims.string FStar_Pervasives_Native.option
val arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStar_Getopt.opt_variant
val pp_validate_dir : option_val -> option_val
val pp_lowercase : option_val -> option_val
val abort_counter : Prims.int FStar_Compiler_Effect.ref
val interp_quake_arg : Prims.string -> Prims.int * Prims.int * Prims.bool
val uu___447 :
  ((Prims.string -> Prims.unit) -> Prims.unit) * (Prims.string -> Prims.unit)
val set_option_warning_callback_aux :
  (Prims.string -> Prims.unit) -> Prims.unit
val option_warning_callback : Prims.string -> Prims.unit
val set_option_warning_callback : (Prims.string -> Prims.unit) -> Prims.unit
val specs_with_types :
  Prims.bool ->
  (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string) Prims.list
val specs : Prims.bool -> FStar_Getopt.opt Prims.list
val settable : Prims.string -> Prims.bool
val all_specs : FStar_Getopt.opt Prims.list
val all_specs_with_types :
  (FStar_BaseTypes.char * Prims.string * opt_type * Prims.string) Prims.list
val settable_specs :
  (FStar_BaseTypes.char * Prims.string *
   Prims.unit FStar_Getopt.opt_variant * Prims.string)
  Prims.list
val uu___638 :
  ((Prims.unit -> FStar_Getopt.parse_cmdline_res) -> Prims.unit) *
  (Prims.unit -> FStar_Getopt.parse_cmdline_res)
val set_error_flags_callback_aux :
  (Prims.unit -> FStar_Getopt.parse_cmdline_res) -> Prims.unit
val set_error_flags : Prims.unit -> FStar_Getopt.parse_cmdline_res
val set_error_flags_callback :
  (Prims.unit -> FStar_Getopt.parse_cmdline_res) -> Prims.unit
val display_usage : Prims.unit -> Prims.unit
val fstar_bin_directory : Prims.string
val file_list_ : Prims.string Prims.list FStar_Compiler_Effect.ref
val parse_filename_arg :
  FStar_Getopt.opt Prims.list ->
  Prims.bool -> Prims.string -> FStar_Getopt.parse_cmdline_res
val parse_cmd_line :
  Prims.unit -> FStar_Getopt.parse_cmdline_res * Prims.string Prims.list
val file_list : Prims.unit -> Prims.string Prims.list
val restore_cmd_line_options : Prims.bool -> FStar_Getopt.parse_cmdline_res
val module_name_of_file_name : Prims.string -> Prims.string
val should_check : Prims.string -> Prims.bool
val should_verify : Prims.string -> Prims.bool
val should_check_file : Prims.string -> Prims.bool
val should_verify_file : Prims.string -> Prims.bool
val module_name_eq : Prims.string -> Prims.string -> Prims.bool
val should_print_message : Prims.string -> Prims.bool
val include_path : Prims.unit -> Prims.string Prims.list
val find_file : Prims.string -> Prims.string FStar_Pervasives_Native.option
val prims : Prims.unit -> Prims.string
val prims_basename : Prims.unit -> Prims.string
val pervasives : Prims.unit -> Prims.string
val pervasives_basename : Prims.unit -> Prims.string
val pervasives_native_basename : Prims.unit -> Prims.string
val prepend_output_dir : Prims.string -> Prims.string
val prepend_cache_dir : Prims.string -> Prims.string
val path_of_text : Prims.string -> Prims.string Prims.list
val parse_settings :
  Prims.string Prims.list ->
  (Prims.string Prims.list * Prims.bool) Prims.list
val __temp_fast_implicits : Prims.unit -> Prims.bool
val admit_smt_queries : Prims.unit -> Prims.bool
val admit_except : Prims.unit -> Prims.string FStar_Pervasives_Native.option
val compat_pre_core_should_register : Prims.unit -> Prims.bool
val compat_pre_core_should_check : Prims.unit -> Prims.bool
val compat_pre_core_set : Prims.unit -> Prims.bool
val compat_pre_typed_indexed_effects : Prims.unit -> Prims.bool
val disallow_unification_guards : Prims.unit -> Prims.bool
val cache_checked_modules : Prims.unit -> Prims.bool
val cache_off : Prims.unit -> Prims.bool
val print_cache_version : Prims.unit -> Prims.bool
val cmi : Prims.unit -> Prims.bool
type codegen_t = OCaml | FSharp | Krml | Plugin
val uu___is_OCaml : codegen_t -> Prims.bool
val uu___is_FSharp : codegen_t -> Prims.bool
val uu___is_Krml : codegen_t -> Prims.bool
val uu___is_Plugin : codegen_t -> Prims.bool
val parse_codegen : Prims.string -> codegen_t FStar_Pervasives_Native.option
val print_codegen : codegen_t -> Prims.string
val codegen : Prims.unit -> codegen_t FStar_Pervasives_Native.option
val codegen_libs : Prims.unit -> Prims.string Prims.list Prims.list
val debug_any : Prims.unit -> Prims.bool
val debug_module : Prims.string -> Prims.bool
val debug_at_level_no_module : debug_level_t -> Prims.bool
val debug_at_level : Prims.string -> debug_level_t -> Prims.bool
val profile_group_by_decls : Prims.unit -> Prims.bool
val defensive : Prims.unit -> Prims.bool
val defensive_error : Prims.unit -> Prims.bool
val defensive_abort : Prims.unit -> Prims.bool
val dep : Prims.unit -> Prims.string FStar_Pervasives_Native.option
val detail_errors : Prims.unit -> Prims.bool
val detail_hint_replay : Prims.unit -> Prims.bool
val dump_module : Prims.string -> Prims.bool
val eager_subtyping : Prims.unit -> Prims.bool
val error_contexts : Prims.unit -> Prims.bool
val expose_interfaces : Prims.unit -> Prims.bool
val force : Prims.unit -> Prims.bool
val full_context_dependency : Prims.unit -> Prims.bool
val hide_uvar_nums : Prims.unit -> Prims.bool
val hint_info : Prims.unit -> Prims.bool
val hint_dir : Prims.unit -> Prims.string FStar_Pervasives_Native.option
val hint_file : Prims.unit -> Prims.string FStar_Pervasives_Native.option
val hint_file_for_src : Prims.string -> Prims.string
val ide : Prims.unit -> Prims.bool
val ide_id_info_off : Prims.unit -> Prims.bool
val print : Prims.unit -> Prims.bool
val print_in_place : Prims.unit -> Prims.bool
val initial_fuel : Prims.unit -> Prims.int
val initial_ifuel : Prims.unit -> Prims.int
val interactive : Prims.unit -> Prims.bool
val lax : Prims.unit -> Prims.bool
val load : Prims.unit -> Prims.string Prims.list
val load_cmxs : Prims.unit -> Prims.string Prims.list
val legacy_interactive : Prims.unit -> Prims.bool
val lsp_server : Prims.unit -> Prims.bool
val log_queries : Prims.unit -> Prims.bool
val keep_query_captions : Prims.unit -> Prims.bool
val log_types : Prims.unit -> Prims.bool
val max_fuel : Prims.unit -> Prims.int
val max_ifuel : Prims.unit -> Prims.int
val ml_ish : Prims.unit -> Prims.bool
val set_ml_ish : Prims.unit -> Prims.unit
val no_default_includes : Prims.unit -> Prims.bool
val no_extract : Prims.string -> Prims.bool
val normalize_pure_terms_for_extraction : Prims.unit -> Prims.bool
val no_location_info : Prims.unit -> Prims.bool
val no_plugins : Prims.unit -> Prims.bool
val no_smt : Prims.unit -> Prims.bool
val output_dir : Prims.unit -> Prims.string FStar_Pervasives_Native.option
val ugly : Prims.unit -> Prims.bool
val print_bound_var_types : Prims.unit -> Prims.bool
val print_effect_args : Prims.unit -> Prims.bool
val print_expected_failures : Prims.unit -> Prims.bool
val print_implicits : Prims.unit -> Prims.bool
val print_real_names : Prims.unit -> Prims.bool
val print_universes : Prims.unit -> Prims.bool
val print_z3_statistics : Prims.unit -> Prims.bool
val quake_lo : Prims.unit -> Prims.int
val quake_hi : Prims.unit -> Prims.int
val quake_keep : Prims.unit -> Prims.bool
val query_stats : Prims.unit -> Prims.bool
val record_hints : Prims.unit -> Prims.bool
val record_options : Prims.unit -> Prims.bool
val retry : Prims.unit -> Prims.bool
val reuse_hint_for :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option
val report_assumes :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option
val silent : Prims.unit -> Prims.bool
val smtencoding_elim_box : Prims.unit -> Prims.bool
val smtencoding_nl_arith_native : Prims.unit -> Prims.bool
val smtencoding_nl_arith_wrapped : Prims.unit -> Prims.bool
val smtencoding_nl_arith_default : Prims.unit -> Prims.bool
val smtencoding_l_arith_native : Prims.unit -> Prims.bool
val smtencoding_l_arith_default : Prims.unit -> Prims.bool
val smtencoding_valid_intro : Prims.unit -> Prims.bool
val smtencoding_valid_elim : Prims.unit -> Prims.bool
val split_queries : Prims.unit -> Prims.bool
val tactic_raw_binders : Prims.unit -> Prims.bool
val tactics_failhard : Prims.unit -> Prims.bool
val tactics_info : Prims.unit -> Prims.bool
val tactic_trace : Prims.unit -> Prims.bool
val tactic_trace_d : Prims.unit -> Prims.int
val tactics_nbe : Prims.unit -> Prims.bool
val tcnorm : Prims.unit -> Prims.bool
val timing : Prims.unit -> Prims.bool
val trace_error : Prims.unit -> Prims.bool
val unthrottle_inductives : Prims.unit -> Prims.bool
val unsafe_tactic_exec : Prims.unit -> Prims.bool
val use_eq_at_higher_order : Prims.unit -> Prims.bool
val use_hints : Prims.unit -> Prims.bool
val use_hint_hashes : Prims.unit -> Prims.bool
val use_native_tactics :
  Prims.unit -> Prims.string FStar_Pervasives_Native.option
val use_tactics : Prims.unit -> Prims.bool
val using_facts_from :
  Prims.unit -> (Prims.string Prims.list * Prims.bool) Prims.list
val warn_default_effects : Prims.unit -> Prims.bool
val warn_error : Prims.unit -> Prims.string
val z3_exe : Prims.unit -> Prims.string
val z3_cliopt : Prims.unit -> Prims.string Prims.list
val z3_smtopt : Prims.unit -> Prims.string Prims.list
val z3_refresh : Prims.unit -> Prims.bool
val z3_rlimit : Prims.unit -> Prims.int
val z3_rlimit_factor : Prims.unit -> Prims.int
val z3_seed : Prims.unit -> Prims.int
val no_positivity : Prims.unit -> Prims.bool
val use_nbe : Prims.unit -> Prims.bool
val use_nbe_for_extraction : Prims.unit -> Prims.bool
val trivial_pre_for_unannotated_effectful_fns : Prims.unit -> Prims.bool
val with_saved_options : (Prims.unit -> 'a) -> 'a
val module_matches_namespace_filter :
  Prims.string -> Prims.string Prims.list -> Prims.bool
val matches_namespace_filter_opt :
  Prims.string ->
  Prims.string Prims.list FStar_Pervasives_Native.option -> Prims.bool
type parsed_extract_setting = {
  target_specific_settings : (codegen_t * Prims.string) Prims.list;
  default_settings : Prims.string FStar_Pervasives_Native.option;
}
val __proj__Mkparsed_extract_setting__item__target_specific_settings :
  parsed_extract_setting -> (codegen_t * Prims.string) Prims.list
val __proj__Mkparsed_extract_setting__item__default_settings :
  parsed_extract_setting -> Prims.string FStar_Pervasives_Native.option
val print_pes : parsed_extract_setting -> Prims.string
val find_setting_for_target :
  codegen_t ->
  (codegen_t * Prims.string) Prims.list ->
  Prims.string FStar_Pervasives_Native.option
val extract_settings :
  Prims.unit -> parsed_extract_setting FStar_Pervasives_Native.option
val should_extract : Prims.string -> codegen_t -> Prims.bool
val should_be_already_cached : Prims.string -> Prims.bool
val profile_enabled :
  Prims.string FStar_Pervasives_Native.option -> Prims.string -> Prims.bool
exception File_argument of Prims.string
val uu___is_File_argument : Prims.exn -> Prims.bool
val __proj__File_argument__item__uu___ : Prims.exn -> Prims.string
val set_options : Prims.string -> FStar_Getopt.parse_cmdline_res
val get_vconfig : Prims.unit -> FStar_VConfig.vconfig
val set_vconfig : FStar_VConfig.vconfig -> Prims.unit

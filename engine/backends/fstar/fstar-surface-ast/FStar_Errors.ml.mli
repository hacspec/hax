exception Invalid_warn_error_setting of Prims.string
val uu___is_Invalid_warn_error_setting : Prims.exn -> Prims.bool
val __proj__Invalid_warn_error_setting__item__uu___ :
  Prims.exn -> Prims.string
val lookup_error :
  ('uuuuu * 'uuuuu1 * 'uuuuu2) Prims.list ->
  'uuuuu -> 'uuuuu * 'uuuuu1 * 'uuuuu2
val lookup_error_range :
  ('uuuuu * 'uuuuu1 * Prims.int) Prims.list ->
  Prims.int * Prims.int -> ('uuuuu * 'uuuuu1 * Prims.int) Prims.list
val error_number : FStar_Errors_Codes.error_setting -> Prims.int
val errno : FStar_Errors_Codes.raw_error -> Prims.int
val warn_on_use_errno : Prims.int
val defensive_errno : Prims.int
val call_to_erased_errno : Prims.int
val update_flags :
  (FStar_Errors_Codes.error_flag * Prims.string) Prims.list ->
  FStar_Errors_Codes.error_setting Prims.list
type error =
    FStar_Errors_Codes.raw_error * Prims.string *
    FStar_Compiler_Range.range * Prims.string Prims.list
type issue_level = ENotImplemented | EInfo | EWarning | EError
val uu___is_ENotImplemented : issue_level -> Prims.bool
val uu___is_EInfo : issue_level -> Prims.bool
val uu___is_EWarning : issue_level -> Prims.bool
val uu___is_EError : issue_level -> Prims.bool
type issue = {
  issue_msg : Prims.string;
  issue_level : issue_level;
  issue_range : FStar_Compiler_Range.range FStar_Pervasives_Native.option;
  issue_number : Prims.int FStar_Pervasives_Native.option;
  issue_ctx : Prims.string Prims.list;
}
val __proj__Mkissue__item__issue_msg : issue -> Prims.string
val __proj__Mkissue__item__issue_level : issue -> issue_level
val __proj__Mkissue__item__issue_range :
  issue -> FStar_Compiler_Range.range FStar_Pervasives_Native.option
val __proj__Mkissue__item__issue_number :
  issue -> Prims.int FStar_Pervasives_Native.option
val __proj__Mkissue__item__issue_ctx : issue -> Prims.string Prims.list
type error_handler = {
  eh_add_one : issue -> Prims.unit;
  eh_count_errors : Prims.unit -> Prims.int;
  eh_report : Prims.unit -> issue Prims.list;
  eh_clear : Prims.unit -> Prims.unit;
}
val __proj__Mkerror_handler__item__eh_add_one :
  error_handler -> issue -> Prims.unit
val __proj__Mkerror_handler__item__eh_count_errors :
  error_handler -> Prims.unit -> Prims.int
val __proj__Mkerror_handler__item__eh_report :
  error_handler -> Prims.unit -> issue Prims.list
val __proj__Mkerror_handler__item__eh_clear :
  error_handler -> Prims.unit -> Prims.unit
exception Error of error
val uu___is_Error : Prims.exn -> Prims.bool
val __proj__Error__item__uu___ : Prims.exn -> error
exception Err of
            (FStar_Errors_Codes.raw_error * Prims.string *
             Prims.string Prims.list)
val uu___is_Err : Prims.exn -> Prims.bool
val __proj__Err__item__uu___ :
  Prims.exn ->
  FStar_Errors_Codes.raw_error * Prims.string * Prims.string Prims.list
exception Warning of error
val uu___is_Warning : Prims.exn -> Prims.bool
val __proj__Warning__item__uu___ : Prims.exn -> error
exception Stop
val uu___is_Stop : Prims.exn -> Prims.bool
exception Empty_frag
val uu___is_Empty_frag : Prims.exn -> Prims.bool
val ctx_string : Prims.string Prims.list -> Prims.string
val issue_message : issue -> Prims.string
val format_issue : issue -> Prims.string
val print_issue : issue -> Prims.unit
val compare_issues : issue -> issue -> Prims.int
val mk_default_handler : Prims.bool -> error_handler
val default_handler : error_handler
val current_handler : error_handler FStar_Compiler_Effect.ref
val mk_issue :
  issue_level ->
  FStar_Compiler_Range.range FStar_Pervasives_Native.option ->
  Prims.string ->
  Prims.int FStar_Pervasives_Native.option ->
  Prims.string Prims.list -> issue
val get_err_count : Prims.unit -> Prims.int
val wrapped_eh_add_one : error_handler -> issue -> Prims.unit
val add_one : issue -> Prims.unit
val add_many : issue Prims.list -> Prims.unit
val report_all : Prims.unit -> issue Prims.list
val clear : Prims.unit -> Prims.unit
val set_handler : error_handler -> Prims.unit
type error_context_t = {
  push : Prims.string -> Prims.unit;
  pop : Prims.unit -> Prims.string;
  clear : Prims.unit -> Prims.unit;
  get : Prims.unit -> Prims.string Prims.list;
  set : Prims.string Prims.list -> Prims.unit;
}
val __proj__Mkerror_context_t__item__push :
  error_context_t -> Prims.string -> Prims.unit
val __proj__Mkerror_context_t__item__pop :
  error_context_t -> Prims.unit -> Prims.string
val __proj__Mkerror_context_t__item__clear :
  error_context_t -> Prims.unit -> Prims.unit
val __proj__Mkerror_context_t__item__get :
  error_context_t -> Prims.unit -> Prims.string Prims.list
val __proj__Mkerror_context_t__item__set :
  error_context_t -> Prims.string Prims.list -> Prims.unit
val error_context : error_context_t
val get_ctx : Prims.unit -> Prims.string Prims.list
val diag : FStar_Compiler_Range.range -> Prims.string -> Prims.unit
val warn_unsafe_options :
  FStar_Compiler_Range.range FStar_Pervasives_Native.option ->
  Prims.string -> Prims.unit
val set_option_warning_callback_range :
  FStar_Compiler_Range.range FStar_Pervasives_Native.option -> Prims.unit
val uu___279 :
  ((Prims.string -> FStar_Errors_Codes.error_setting Prims.list) ->
   Prims.unit) *
  (Prims.unit -> FStar_Errors_Codes.error_setting Prims.list)
val t_set_parse_warn_error :
  (Prims.string -> FStar_Errors_Codes.error_setting Prims.list) -> Prims.unit
val error_flags : Prims.unit -> FStar_Errors_Codes.error_setting Prims.list
val set_parse_warn_error :
  (Prims.string -> FStar_Errors_Codes.error_setting Prims.list) -> Prims.unit
val lookup : FStar_Errors_Codes.raw_error -> FStar_Errors_Codes.error_setting
val log_issue_ctx :
  FStar_Compiler_Range.range ->
  FStar_Errors_Codes.raw_error * Prims.string ->
  Prims.string Prims.list -> Prims.unit
val log_issue :
  FStar_Compiler_Range.range ->
  FStar_Errors_Codes.raw_error * Prims.string -> Prims.unit
val add_errors : error Prims.list -> Prims.unit
val issue_of_exn : Prims.exn -> issue FStar_Pervasives_Native.option
val err_exn : Prims.exn -> Prims.unit
val handleable : Prims.exn -> Prims.bool
val stop_if_err : Prims.unit -> Prims.unit
val raise_error :
  FStar_Errors_Codes.raw_error * Prims.string ->
  FStar_Compiler_Range.range -> 'a
val raise_err : FStar_Errors_Codes.raw_error * Prims.string -> 'a
val with_ctx : Prims.string -> (Prims.unit -> 'a) -> 'a
val with_ctx_if : Prims.bool -> Prims.string -> (Prims.unit -> 'a) -> 'a
val no_ctx : (Prims.unit -> 'a) -> 'a
val catch_errors :
  (Prims.unit -> 'a) -> issue Prims.list * 'a FStar_Pervasives_Native.option
val find_multiset_discrepancy :
  Prims.int Prims.list ->
  Prims.int Prims.list ->
  (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option

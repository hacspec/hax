open Prims
exception Invalid_warn_error_setting of Prims.string 
let (uu___is_Invalid_warn_error_setting : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Invalid_warn_error_setting uu___ -> true
    | uu___ -> false
let (__proj__Invalid_warn_error_setting__item__uu___ :
  Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | Invalid_warn_error_setting uu___ -> uu___
let lookup_error :
  'uuuuu 'uuuuu1 'uuuuu2 .
    ('uuuuu * 'uuuuu1 * 'uuuuu2) Prims.list ->
      'uuuuu -> ('uuuuu * 'uuuuu1 * 'uuuuu2)
  =
  fun settings ->
    fun e ->
      let uu___ =
        FStar_Compiler_Util.try_find
          (fun uu___1 -> match uu___1 with | (v, uu___2, i) -> e = v)
          settings in
      match uu___ with
      | FStar_Pervasives_Native.Some i -> i
      | FStar_Pervasives_Native.None ->
          failwith "Impossible: unrecognized error"
let lookup_error_range :
  'uuuuu 'uuuuu1 .
    ('uuuuu * 'uuuuu1 * Prims.int) Prims.list ->
      (Prims.int * Prims.int) -> ('uuuuu * 'uuuuu1 * Prims.int) Prims.list
  =
  fun settings ->
    fun uu___ ->
      match uu___ with
      | (l, h) ->
          let uu___1 =
            FStar_Compiler_List.partition
              (fun uu___2 ->
                 match uu___2 with
                 | (uu___3, uu___4, i) -> (l <= i) && (i <= h)) settings in
          (match uu___1 with | (matches, uu___2) -> matches)
let (error_number : FStar_Errors_Codes.error_setting -> Prims.int) =
  fun uu___ -> match uu___ with | (uu___1, uu___2, i) -> i
let (errno : FStar_Errors_Codes.raw_error -> Prims.int) =
  fun e ->
    let uu___ = lookup_error FStar_Errors_Codes.default_settings e in
    error_number uu___
let (warn_on_use_errno : Prims.int) =
  errno FStar_Errors_Codes.Warning_WarnOnUse
let (defensive_errno : Prims.int) =
  errno FStar_Errors_Codes.Warning_Defensive
let (call_to_erased_errno : Prims.int) =
  errno FStar_Errors_Codes.Error_CallToErased
let (update_flags :
  (FStar_Errors_Codes.error_flag * Prims.string) Prims.list ->
    FStar_Errors_Codes.error_setting Prims.list)
  =
  fun l ->
    let set_one_flag i flag default_flag =
      match (flag, default_flag) with
      | (FStar_Errors_Codes.CWarning, FStar_Errors_Codes.CAlwaysError) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Compiler_Util.string_of_int i in
              FStar_Compiler_Util.format1 "cannot turn error %s into warning"
                uu___2 in
            Invalid_warn_error_setting uu___1 in
          FStar_Compiler_Effect.raise uu___
      | (FStar_Errors_Codes.CError, FStar_Errors_Codes.CAlwaysError) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Compiler_Util.string_of_int i in
              FStar_Compiler_Util.format1 "cannot turn error %s into warning"
                uu___2 in
            Invalid_warn_error_setting uu___1 in
          FStar_Compiler_Effect.raise uu___
      | (FStar_Errors_Codes.CSilent, FStar_Errors_Codes.CAlwaysError) ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Compiler_Util.string_of_int i in
              FStar_Compiler_Util.format1 "cannot silence error %s" uu___2 in
            Invalid_warn_error_setting uu___1 in
          FStar_Compiler_Effect.raise uu___
      | (uu___, FStar_Errors_Codes.CFatal) ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Compiler_Util.string_of_int i in
              FStar_Compiler_Util.format1
                "cannot change the error level of fatal error %s" uu___3 in
            Invalid_warn_error_setting uu___2 in
          FStar_Compiler_Effect.raise uu___1
      | uu___ -> flag in
    let set_flag_for_range uu___ =
      match uu___ with
      | (flag, range) ->
          let errs =
            lookup_error_range FStar_Errors_Codes.default_settings range in
          FStar_Compiler_List.map
            (fun uu___1 ->
               match uu___1 with
               | (v, default_flag, i) ->
                   let uu___2 = set_one_flag i flag default_flag in
                   (v, uu___2, i)) errs in
    let compute_range uu___ =
      match uu___ with
      | (flag, s) ->
          let r = FStar_Compiler_Util.split s ".." in
          let uu___1 =
            match r with
            | r1::r2::[] ->
                let uu___2 = FStar_Compiler_Util.int_of_string r1 in
                let uu___3 = FStar_Compiler_Util.int_of_string r2 in
                (uu___2, uu___3)
            | uu___2 ->
                let uu___3 =
                  let uu___4 =
                    FStar_Compiler_Util.format1
                      "Malformed warn-error range %s" s in
                  Invalid_warn_error_setting uu___4 in
                FStar_Compiler_Effect.raise uu___3 in
          (match uu___1 with | (l1, h) -> (flag, (l1, h))) in
    let error_range_settings = FStar_Compiler_List.map compute_range l in
    let uu___ =
      FStar_Compiler_List.collect set_flag_for_range error_range_settings in
    FStar_Compiler_List.op_At uu___ FStar_Errors_Codes.default_settings
type error =
  (FStar_Errors_Codes.raw_error * Prims.string * FStar_Compiler_Range.range *
    Prims.string Prims.list)
type issue_level =
  | ENotImplemented 
  | EInfo 
  | EWarning 
  | EError 
let (uu___is_ENotImplemented : issue_level -> Prims.bool) =
  fun projectee ->
    match projectee with | ENotImplemented -> true | uu___ -> false
let (uu___is_EInfo : issue_level -> Prims.bool) =
  fun projectee -> match projectee with | EInfo -> true | uu___ -> false
let (uu___is_EWarning : issue_level -> Prims.bool) =
  fun projectee -> match projectee with | EWarning -> true | uu___ -> false
let (uu___is_EError : issue_level -> Prims.bool) =
  fun projectee -> match projectee with | EError -> true | uu___ -> false
type issue =
  {
  issue_msg: Prims.string ;
  issue_level: issue_level ;
  issue_range: FStar_Compiler_Range.range FStar_Pervasives_Native.option ;
  issue_number: Prims.int FStar_Pervasives_Native.option ;
  issue_ctx: Prims.string Prims.list }
let (__proj__Mkissue__item__issue_msg : issue -> Prims.string) =
  fun projectee ->
    match projectee with
    | { issue_msg; issue_level = issue_level1; issue_range; issue_number;
        issue_ctx;_} -> issue_msg
let (__proj__Mkissue__item__issue_level : issue -> issue_level) =
  fun projectee ->
    match projectee with
    | { issue_msg; issue_level = issue_level1; issue_range; issue_number;
        issue_ctx;_} -> issue_level1
let (__proj__Mkissue__item__issue_range :
  issue -> FStar_Compiler_Range.range FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { issue_msg; issue_level = issue_level1; issue_range; issue_number;
        issue_ctx;_} -> issue_range
let (__proj__Mkissue__item__issue_number :
  issue -> Prims.int FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { issue_msg; issue_level = issue_level1; issue_range; issue_number;
        issue_ctx;_} -> issue_number
let (__proj__Mkissue__item__issue_ctx : issue -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { issue_msg; issue_level = issue_level1; issue_range; issue_number;
        issue_ctx;_} -> issue_ctx
type error_handler =
  {
  eh_add_one: issue -> unit ;
  eh_count_errors: unit -> Prims.int ;
  eh_report: unit -> issue Prims.list ;
  eh_clear: unit -> unit }
let (__proj__Mkerror_handler__item__eh_add_one :
  error_handler -> issue -> unit) =
  fun projectee ->
    match projectee with
    | { eh_add_one; eh_count_errors; eh_report; eh_clear;_} -> eh_add_one
let (__proj__Mkerror_handler__item__eh_count_errors :
  error_handler -> unit -> Prims.int) =
  fun projectee ->
    match projectee with
    | { eh_add_one; eh_count_errors; eh_report; eh_clear;_} ->
        eh_count_errors
let (__proj__Mkerror_handler__item__eh_report :
  error_handler -> unit -> issue Prims.list) =
  fun projectee ->
    match projectee with
    | { eh_add_one; eh_count_errors; eh_report; eh_clear;_} -> eh_report
let (__proj__Mkerror_handler__item__eh_clear : error_handler -> unit -> unit)
  =
  fun projectee ->
    match projectee with
    | { eh_add_one; eh_count_errors; eh_report; eh_clear;_} -> eh_clear
exception Error of error 
let (uu___is_Error : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Error uu___ -> true | uu___ -> false
let (__proj__Error__item__uu___ : Prims.exn -> error) =
  fun projectee -> match projectee with | Error uu___ -> uu___
exception Err of (FStar_Errors_Codes.raw_error * Prims.string * Prims.string
  Prims.list) 
let (uu___is_Err : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | Err uu___ -> true | uu___ -> false
let (__proj__Err__item__uu___ :
  Prims.exn ->
    (FStar_Errors_Codes.raw_error * Prims.string * Prims.string Prims.list))
  = fun projectee -> match projectee with | Err uu___ -> uu___
exception Warning of error 
let (uu___is_Warning : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning uu___ -> true | uu___ -> false
let (__proj__Warning__item__uu___ : Prims.exn -> error) =
  fun projectee -> match projectee with | Warning uu___ -> uu___
exception Stop 
let (uu___is_Stop : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | Stop -> true | uu___ -> false
exception Empty_frag 
let (uu___is_Empty_frag : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | Empty_frag -> true | uu___ -> false
let (ctx_string : Prims.string Prims.list -> Prims.string) =
  fun ctx -> ""
let (issue_message : issue -> Prims.string) =
  fun i ->
    let uu___ = ctx_string i.issue_ctx in
    FStar_String.op_Hat i.issue_msg uu___
let (format_issue : issue -> Prims.string) =
  fun issue1 ->
    let level_header =
      match issue1.issue_level with
      | EInfo -> "Info"
      | EWarning -> "Warning"
      | EError -> "Error"
      | ENotImplemented -> "Feature not yet implemented: " in
    let uu___ =
      match issue1.issue_range with
      | FStar_Pervasives_Native.None -> ("", "")
      | FStar_Pervasives_Native.Some r when
          r = FStar_Compiler_Range.dummyRange ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Compiler_Range.def_range r in
              let uu___4 =
                FStar_Compiler_Range.def_range
                  FStar_Compiler_Range.dummyRange in
              uu___3 = uu___4 in
            if uu___2
            then ""
            else
              (let uu___4 = FStar_Compiler_Range.string_of_range r in
               FStar_Compiler_Util.format1 " (see also %s)" uu___4) in
          ("", uu___1)
      | FStar_Pervasives_Native.Some r ->
          let uu___1 =
            let uu___2 = FStar_Compiler_Range.string_of_use_range r in
            FStar_Compiler_Util.format1 "%s: " uu___2 in
          let uu___2 =
            let uu___3 =
              (let uu___4 = FStar_Compiler_Range.use_range r in
               let uu___5 = FStar_Compiler_Range.def_range r in
               uu___4 = uu___5) ||
                (let uu___4 = FStar_Compiler_Range.def_range r in
                 let uu___5 =
                   FStar_Compiler_Range.def_range
                     FStar_Compiler_Range.dummyRange in
                 uu___4 = uu___5) in
            if uu___3
            then ""
            else
              (let uu___5 = FStar_Compiler_Range.string_of_range r in
               FStar_Compiler_Util.format1 " (see also %s)" uu___5) in
          (uu___1, uu___2) in
    match uu___ with
    | (range_str, see_also_str) ->
        let issue_number =
          match issue1.issue_number with
          | FStar_Pervasives_Native.None -> ""
          | FStar_Pervasives_Native.Some n ->
              let uu___1 = FStar_Compiler_Util.string_of_int n in
              FStar_Compiler_Util.format1 " %s" uu___1 in
        let uu___1 = issue_message issue1 in
        FStar_Compiler_Util.format5 "%s(%s%s) %s%s" range_str level_header
          issue_number uu___1 see_also_str
let (print_issue : issue -> unit) =
  fun issue1 ->
    let printer =
      match issue1.issue_level with
      | EInfo -> FStar_Compiler_Util.print_string
      | EWarning -> FStar_Compiler_Util.print_warning
      | EError -> FStar_Compiler_Util.print_error
      | ENotImplemented -> FStar_Compiler_Util.print_error in
    let uu___ =
      let uu___1 = format_issue issue1 in FStar_String.op_Hat uu___1 "\n" in
    printer uu___
let (compare_issues : issue -> issue -> Prims.int) =
  fun i1 ->
    fun i2 ->
      match ((i1.issue_range), (i2.issue_range)) with
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
          Prims.int_zero
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some uu___) ->
          ~- Prims.int_one
      | (FStar_Pervasives_Native.Some uu___, FStar_Pervasives_Native.None) ->
          Prims.int_one
      | (FStar_Pervasives_Native.Some r1, FStar_Pervasives_Native.Some r2) ->
          FStar_Compiler_Range.compare_use_range r1 r2
let (mk_default_handler : Prims.bool -> error_handler) =
  fun print ->
    let issues = FStar_Compiler_Util.mk_ref [] in
    let err_count = FStar_Compiler_Util.mk_ref Prims.int_zero in
    let add_one e =
      if e.issue_level = EError
      then
        (let uu___1 =
           let uu___2 = FStar_Compiler_Effect.op_Bang err_count in
           Prims.int_one + uu___2 in
         FStar_Compiler_Effect.op_Colon_Equals err_count uu___1)
      else ();
      (match e.issue_level with
       | EInfo -> print_issue e
       | uu___2 ->
           let uu___3 =
             let uu___4 = FStar_Compiler_Effect.op_Bang issues in e :: uu___4 in
           FStar_Compiler_Effect.op_Colon_Equals issues uu___3);
      (let uu___3 =
         (false) &&
           (e.issue_number = (FStar_Pervasives_Native.Some defensive_errno)) in
       if uu___3 then failwith "Aborting due to --defensive abort" else ()) in
    let count_errors uu___ = FStar_Compiler_Effect.op_Bang err_count in
    let report uu___ =
      let unique_issues =
        let uu___1 = FStar_Compiler_Effect.op_Bang issues in
        FStar_Compiler_Util.remove_dups (fun i0 -> fun i1 -> i0 = i1) uu___1 in
      let sorted_unique_issues =
        FStar_Compiler_List.sortWith compare_issues unique_issues in
      if print
      then FStar_Compiler_List.iter print_issue sorted_unique_issues
      else ();
      sorted_unique_issues in
    let clear uu___ =
      FStar_Compiler_Effect.op_Colon_Equals issues [];
      FStar_Compiler_Effect.op_Colon_Equals err_count Prims.int_zero in
    {
      eh_add_one = add_one;
      eh_count_errors = count_errors;
      eh_report = report;
      eh_clear = clear
    }
let (default_handler : error_handler) = mk_default_handler true
let (current_handler : error_handler FStar_Compiler_Effect.ref) =
  FStar_Compiler_Util.mk_ref default_handler
let (mk_issue :
  issue_level ->
    FStar_Compiler_Range.range FStar_Pervasives_Native.option ->
      Prims.string ->
        Prims.int FStar_Pervasives_Native.option ->
          Prims.string Prims.list -> issue)
  =
  fun level ->
    fun range ->
      fun msg ->
        fun n ->
          fun ctx ->
            {
              issue_msg = msg;
              issue_level = level;
              issue_range = range;
              issue_number = n;
              issue_ctx = ctx
            }
let (get_err_count : unit -> Prims.int) =
  fun uu___ ->
    let uu___1 = FStar_Compiler_Effect.op_Bang current_handler in
    uu___1.eh_count_errors ()
let (wrapped_eh_add_one : error_handler -> issue -> unit) =
  fun h ->
    fun issue1 ->
      h.eh_add_one issue1;
      ()
let (add_one : issue -> unit) =
  fun issue1 ->
      (
         let uu___1 = FStar_Compiler_Effect.op_Bang current_handler in
         wrapped_eh_add_one uu___1 issue1)
let (add_many : issue Prims.list -> unit) =
  fun issues ->
      (
         let uu___1 =
           let uu___2 = FStar_Compiler_Effect.op_Bang current_handler in
           wrapped_eh_add_one uu___2 in
         FStar_Compiler_List.iter uu___1 issues)
let (report_all : unit -> issue Prims.list) =
  fun uu___ ->
    let uu___1 = FStar_Compiler_Effect.op_Bang current_handler in
    uu___1.eh_report ()
let (clear : unit -> unit) =
  fun uu___ ->
    let uu___1 = FStar_Compiler_Effect.op_Bang current_handler in
    uu___1.eh_clear ()
let (set_handler : error_handler -> unit) =
  fun handler ->
    let issues = report_all () in
    clear ();
    FStar_Compiler_Effect.op_Colon_Equals current_handler handler;
    add_many issues
type error_context_t =
  {
  push: Prims.string -> unit ;
  pop: unit -> Prims.string ;
  clear: unit -> unit ;
  get: unit -> Prims.string Prims.list ;
  set: Prims.string Prims.list -> unit }
let (__proj__Mkerror_context_t__item__push :
  error_context_t -> Prims.string -> unit) =
  fun projectee ->
    match projectee with | { push; pop; clear = clear1; get; set;_} -> push
let (__proj__Mkerror_context_t__item__pop :
  error_context_t -> unit -> Prims.string) =
  fun projectee ->
    match projectee with | { push; pop; clear = clear1; get; set;_} -> pop
let (__proj__Mkerror_context_t__item__clear :
  error_context_t -> unit -> unit) =
  fun projectee ->
    match projectee with | { push; pop; clear = clear1; get; set;_} -> clear1
let (__proj__Mkerror_context_t__item__get :
  error_context_t -> unit -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with | { push; pop; clear = clear1; get; set;_} -> get
let (__proj__Mkerror_context_t__item__set :
  error_context_t -> Prims.string Prims.list -> unit) =
  fun projectee ->
    match projectee with | { push; pop; clear = clear1; get; set;_} -> set
let (error_context : error_context_t) =
  let ctxs = FStar_Compiler_Util.mk_ref [] in
  let push s =
    let uu___ =
      let uu___1 = FStar_Compiler_Effect.op_Bang ctxs in s :: uu___1 in
    FStar_Compiler_Effect.op_Colon_Equals ctxs uu___ in
  let pop s =
    let uu___ = FStar_Compiler_Effect.op_Bang ctxs in
    match uu___ with
    | h::t -> (FStar_Compiler_Effect.op_Colon_Equals ctxs t; h)
    | uu___1 -> failwith "cannot pop error prefix..." in
  let clear1 uu___ = FStar_Compiler_Effect.op_Colon_Equals ctxs [] in
  let get uu___ = FStar_Compiler_Effect.op_Bang ctxs in
  let set c = FStar_Compiler_Effect.op_Colon_Equals ctxs c in
  { push; pop; clear = clear1; get; set }
let (get_ctx : unit -> Prims.string Prims.list) =
  fun uu___ -> error_context.get ()
let (diag : FStar_Compiler_Range.range -> Prims.string -> unit) =
  fun r ->
    fun msg ->
      if false
      then
        add_one
          (mk_issue EInfo (FStar_Pervasives_Native.Some r) msg
             FStar_Pervasives_Native.None [])
      else ()
let (warn_unsafe_options :
  FStar_Compiler_Range.range FStar_Pervasives_Native.option ->
    Prims.string -> unit)
  =
  fun rng_opt ->
    fun msg -> ()
let (set_option_warning_callback_range :
  FStar_Compiler_Range.range FStar_Pervasives_Native.option -> unit) =
  fun ropt ->
    ()
    (* FStar_Options.set_option_warning_callback (warn_unsafe_options ropt) *)
let (uu___279 :
  (((Prims.string -> FStar_Errors_Codes.error_setting Prims.list) -> unit) *
    (unit -> FStar_Errors_Codes.error_setting Prims.list)))
  =
  let parser_callback =
    FStar_Compiler_Util.mk_ref FStar_Pervasives_Native.None in
  (* let error_flags = FStar_Compiler_Util.smap_create (Prims.of_int (10)) in *)
  let set_error_flags uu___ = () in
  let get_error_flags uu___ =
     FStar_Errors_Codes.default_settings in
  let set_callbacks f =
    FStar_Compiler_Effect.op_Colon_Equals parser_callback
      (FStar_Pervasives_Native.Some f)
    (* FStar_Options.set_option_warning_callback *)
    (*   (warn_unsafe_options FStar_Pervasives_Native.None) *)
  in
  (set_callbacks, get_error_flags)
let (t_set_parse_warn_error :
  (Prims.string -> FStar_Errors_Codes.error_setting Prims.list) -> unit) =
  match uu___279 with
  | (t_set_parse_warn_error1, error_flags) -> t_set_parse_warn_error1
let (error_flags : unit -> FStar_Errors_Codes.error_setting Prims.list) =
  match uu___279 with
  | (t_set_parse_warn_error1, error_flags1) -> error_flags1
let (set_parse_warn_error :
  (Prims.string -> FStar_Errors_Codes.error_setting Prims.list) -> unit) =
  t_set_parse_warn_error
let (lookup :
  FStar_Errors_Codes.raw_error -> FStar_Errors_Codes.error_setting) =
  fun err ->
    let flags = error_flags () in
    let uu___ = lookup_error flags err in
    match uu___ with
    | (v, level, i) ->
        let with_level level1 = (v, level1, i) in
        (match v with
         | uu___1 -> with_level level)

let raise_error :
  'a .
    (FStar_Errors_Codes.raw_error * Prims.string) ->
      FStar_Compiler_Range.range -> 'a
  =
  fun uu___ ->
    fun r ->
      match uu___ with
      | (e, msg) ->
          let uu___1 =
            let uu___2 =
              let uu___3 = error_context.get () in (e, msg, r, uu___3) in
            Error uu___2 in
          FStar_Compiler_Effect.raise uu___1
let raise_err : 'a . (FStar_Errors_Codes.raw_error * Prims.string) -> 'a =
  fun uu___ ->
    match uu___ with
    | (e, msg) ->
        let uu___1 =
          let uu___2 = let uu___3 = error_context.get () in (e, msg, uu___3) in
          Err uu___2 in
        FStar_Compiler_Effect.raise uu___1

let (log_issue_ctx :
  FStar_Compiler_Range.range ->
    (FStar_Errors_Codes.raw_error * Prims.string) ->
      Prims.string Prims.list -> unit)
  =
  fun r ->
    fun uu___ ->
      fun ctx ->
        match uu___ with
        | (e, msg) ->
            let uu___1 = lookup e in
            (match uu___1 with
             | (uu___2, FStar_Errors_Codes.CAlwaysError, errno1) ->
                 add_one
                   (mk_issue EError (FStar_Pervasives_Native.Some r) msg
                      (FStar_Pervasives_Native.Some errno1) ctx)
             | (uu___2, FStar_Errors_Codes.CError, errno1) ->
                 add_one
                   (mk_issue EError (FStar_Pervasives_Native.Some r) msg
                      (FStar_Pervasives_Native.Some errno1) ctx)
             | (uu___2, FStar_Errors_Codes.CWarning, errno1) ->
                 add_one
                   (mk_issue EWarning (FStar_Pervasives_Native.Some r) msg
                      (FStar_Pervasives_Native.Some errno1) ctx)
             | (uu___2, FStar_Errors_Codes.CSilent, uu___3) -> ()
             | (uu___2, FStar_Errors_Codes.CFatal, errno1) ->
                 let i =
                   mk_issue EError (FStar_Pervasives_Native.Some r) msg
                     (FStar_Pervasives_Native.Some errno1) ctx in
                 let uu___3 = false in
                 if uu___3
                 then add_one i
                 else
                   (let uu___5 =
                      let uu___6 = format_issue i in
                      FStar_String.op_Hat
                        "don't use log_issue to report fatal error, should use raise_error: "
                        uu___6 in
                    failwith uu___5))
let (log_issue :
  FStar_Compiler_Range.range ->
    (FStar_Errors_Codes.raw_error * Prims.string) -> unit)
  =
  fun r ->
    fun uu___ ->
      match uu___ with
      | (e, msg) ->
          let ctx = error_context.get () in log_issue_ctx r (e, msg) ctx

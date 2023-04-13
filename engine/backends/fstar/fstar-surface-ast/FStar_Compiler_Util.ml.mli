val max_int : Z.t
val is_letter : int -> bool
val is_digit : int -> bool
val is_letter_or_digit : int -> bool
val is_symbol : int -> bool
val is_punctuation : int -> bool
val return_all : 'a -> 'a
type time = float
val now : unit -> float
val now_ms : unit -> Z.t
val time_diff : time -> time -> float * Prims.int
val record_time : (unit -> 'a) -> 'a * Prims.int
val get_file_last_modification_time : string -> float
val is_before : 'a -> 'a -> bool
val string_of_time : float -> string
exception Impos
val cur_sigint_handler : Sys.signal_behavior ref
exception SigInt
type sigint_handler = Sys.signal_behavior
val sigint_ignore : sigint_handler
val sigint_delay : int ref
val sigint_pending : bool ref
val raise_sigint : 'a -> 'b
val raise_sigint_maybe_delay : 'a -> unit
val sigint_raise : sigint_handler
val set_sigint_handler : Sys.signal_behavior -> unit
val with_sigint_handler : Sys.signal_behavior -> (unit -> 'a) -> 'a
type proc = {
  pid : int;
  inc : in_channel;
  outc : out_channel;
  mutable killed : bool;
  stop_marker : (string -> bool) option;
  id : string;
  start_time : time;
}
val all_procs : proc list ref
val lock : unit -> unit
val release : unit -> unit
val sleep : Z.t -> unit
val mlock : Mutex.t
val monitor_enter : 'a -> unit
val monitor_exit : 'a -> unit
val monitor_wait : 'a -> unit
val monitor_pulse : 'a -> unit
val current_tid : 'a -> Z.t
val atomically : (unit -> 'a) -> 'a
val with_monitor : 'a -> ('b -> 'c) -> 'b -> 'c
val spawn : (unit -> 'a) -> unit
val stack_dump : unit -> string
val start_process' :
  string -> string -> string list -> (string -> bool) option -> proc
val start_process :
  string -> string -> string list -> (string -> bool) -> proc
val waitpid_ignore_signals : int -> unit
val kill_process : proc -> unit
val kill_all : unit -> unit
val process_read_all_output : proc -> string
val process_read_async :
  proc -> string option -> ((unit -> unit) -> 'a) -> unit
val run_process : string -> string -> string list -> string option -> string
type read_result = EOF | SIGINT
val ask_process : proc -> string -> (unit -> string) -> string
val get_file_extension : string -> string
val is_path_absolute : BatPathGen.OfString.ustring -> bool
val join_paths :
  BatPathGen.OfString.ustring -> BatPathGen.OfString.ustring -> string
val normalize_file_path : string -> string
type stream_reader = BatIO.input
val open_stdin : unit -> BatIO.input
val read_line : BatIO.input -> string option
val nread : stream_reader -> Z.t -> string option
val poll_stdin : float -> bool
type string_builder = BatBuffer.t
val new_string_builder : unit -> BatBuffer.t
val clear_string_builder : BatBuffer.t -> unit
val string_of_string_builder : BatBuffer.t -> string
val string_builder_append : BatBuffer.t -> string -> unit
val message_of_exn : exn -> string
val trace_of_exn : exn -> string
type 'a set = 'a list * ('a -> 'a -> bool)
val pp_set :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  Ppx_deriving_runtime.Format.formatter ->
  'a set -> Ppx_deriving_runtime.unit
val show_set :
  (Ppx_deriving_runtime.Format.formatter -> 'a -> Ppx_deriving_runtime.unit) ->
  'a set -> Ppx_deriving_runtime.string
val set_to_yojson : 'a -> 'b -> [> `Null ]
val set_of_yojson : 'a -> 'b -> 'c
val set_is_empty : 'a set -> bool
val as_set : 'a list -> ('a -> 'a -> Z.t) -> 'a list * ('a -> 'a -> bool)
val new_set : ('a -> 'a -> Z.t) -> 'a set
val set_elements : 'a set -> 'a list
val set_add : 'a -> 'a set -> 'a list * ('a -> 'a -> bool)
val set_remove : 'a -> 'a set -> 'a list * ('a -> 'a -> bool)
val set_mem : 'a -> 'a set -> bool
val set_union : 'a set -> 'a set -> 'a list * ('a -> 'a -> bool)
val set_intersect : 'a set -> 'a set -> 'a list * ('a -> 'a -> bool)
val set_is_subset_of : 'a set -> 'a set -> bool
val set_count : 'a set -> Z.t
val set_difference : 'a set -> 'a set -> 'a set
val set_symmetric_difference : 'a set -> 'a set -> 'a set
val set_eq : 'a set -> 'a set -> bool
module StringOps :
  sig
    type t = string
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val hash : t -> int
  end
module StringHashtbl :
  sig
    type key = StringOps.t
    type 'a t = 'a BatHashtbl.Make(StringOps).t
    val create : int -> 'a t
    val length : 'a t -> int
    val is_empty : 'a t -> bool
    val clear : 'a t -> unit
    val copy : 'a t -> 'a t
    val add : 'a t -> key -> 'a -> unit
    val remove : 'a t -> key -> unit
    val remove_all : 'a t -> key -> unit
    val find : 'a t -> key -> 'a
    val find_all : 'a t -> key -> 'a list
    val find_default : 'a t -> key -> 'a -> 'a
    val find_option : 'a t -> key -> 'a option
    val replace : 'a t -> key -> 'a -> unit
    val mem : 'a t -> key -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val for_all : (key -> 'a -> bool) -> 'a t -> bool
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val exists : (key -> 'a -> bool) -> 'a t -> bool
    val map : (key -> 'b -> 'c) -> 'b t -> 'c t
    val map_inplace : (key -> 'a -> 'a) -> 'a t -> unit
    val filter : ('a -> bool) -> 'a t -> 'a t
    val filter_inplace : ('a -> bool) -> 'a t -> unit
    val filteri : (key -> 'a -> bool) -> 'a t -> 'a t
    val filteri_inplace : (key -> 'a -> bool) -> 'a t -> unit
    val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t
    val filter_map_inplace : (key -> 'a -> 'a option) -> 'a t -> unit
    val modify : key -> ('a -> 'a) -> 'a t -> unit
    val modify_def : 'a -> key -> ('a -> 'a) -> 'a t -> unit
    val modify_opt : key -> ('a option -> 'a option) -> 'a t -> unit
    val merge :
      (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
    val merge_all :
      (key -> 'a list -> 'b list -> 'c list) -> 'a t -> 'b t -> 'c t
    val stats : 'a t -> BatHashtbl.statistics
    val keys : 'a t -> key BatEnum.t
    val values : 'a t -> 'a BatEnum.t
    val enum : 'a t -> (key * 'a) BatEnum.t
    val to_list : 'a t -> (key * 'a) list
    val of_enum : (key * 'a) BatEnum.t -> 'a t
    val of_list : (key * 'a) list -> 'a t
    val print :
      ?first:string ->
      ?last:string ->
      ?sep:string ->
      ('a BatInnerIO.output -> key -> unit) ->
      ('a BatInnerIO.output -> 'b -> unit) ->
      'a BatInnerIO.output -> 'b t -> unit
    module Exceptionless :
      sig
        val find : 'a t -> key -> 'a option
        val modify :
          key -> ('a -> 'a) -> 'a t -> (unit, exn) BatPervasives.result
      end
    module Infix :
      sig
        val ( --> ) : 'a t -> key -> 'a
        val ( <-- ) : 'a t -> key * 'a -> unit
      end
    module Labels :
      sig
        val add : 'a t -> key:key -> data:'a -> unit
        val replace : 'a t -> key:key -> data:'a -> unit
        val iter : f:(key:key -> data:'a -> unit) -> 'a t -> unit
        val for_all : f:(key:key -> data:'a -> bool) -> 'a t -> bool
        val map : f:(key:key -> data:'a -> 'b) -> 'a t -> 'b t
        val map_inplace : f:(key:key -> data:'a -> 'a) -> 'a t -> unit
        val filter : f:('a -> bool) -> 'a t -> 'a t
        val filter_inplace : f:('a -> bool) -> 'a t -> unit
        val filteri : f:(key:key -> data:'a -> bool) -> 'a t -> 'a t
        val filteri_inplace : f:(key:key -> data:'a -> bool) -> 'a t -> unit
        val filter_map : f:(key:key -> data:'a -> 'b option) -> 'a t -> 'b t
        val filter_map_inplace :
          f:(key:key -> data:'a -> 'a option) -> 'a t -> unit
        val fold :
          f:(key:key -> data:'a -> 'b -> 'b) -> 'a t -> init:'b -> 'b
        val exists : f:(key:key -> data:'a -> bool) -> 'a t -> bool
        val modify : key:key -> f:('a -> 'a) -> 'a t -> unit
        val modify_def :
          default:'a -> key:key -> f:('a -> 'a) -> 'a t -> unit
        val modify_opt :
          key:key -> f:('a option -> 'a option) -> 'a t -> unit
        val merge :
          f:(key -> 'a option -> 'b option -> 'c option) ->
          left:'a t -> right:'b t -> 'c t
        val merge_all :
          f:(key -> 'a list -> 'b list -> 'c list) ->
          left:'a t -> right:'b t -> 'c t
      end
  end
module StringMap :
  sig
    type key = StringOps.t
    type 'a t = 'a BatMap.Make(StringOps).t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val cardinal : 'a t -> int
    val add : key -> 'a -> 'a t -> 'a t
    val update_stdlib : key -> ('a option -> 'a option) -> 'a t -> 'a t
    val update : key -> key -> 'a -> 'a t -> 'a t
    val find : key -> 'a t -> 'a
    val find_opt : key -> 'a t -> 'a option
    val find_default : 'a -> key -> 'a t -> 'a
    val find_first : (key -> bool) -> 'a t -> key * 'a
    val find_first_opt : (key -> bool) -> 'a t -> (key * 'a) option
    val find_last : (key -> bool) -> 'a t -> key * 'a
    val find_last_opt : (key -> bool) -> 'a t -> (key * 'a) option
    val remove : key -> 'a t -> 'a t
    val remove_exn : key -> 'a t -> 'a t
    val modify : key -> ('a -> 'a) -> 'a t -> 'a t
    val modify_def : 'a -> key -> ('a -> 'a) -> 'a t -> 'a t
    val modify_opt : key -> ('a option -> 'a option) -> 'a t -> 'a t
    val extract : key -> 'a t -> 'a * 'a t
    val pop : 'a t -> (key * 'a) * 'a t
    val mem : key -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val filterv : ('a -> bool) -> 'a t -> 'a t
    val filter : (key -> 'a -> bool) -> 'a t -> 'a t
    val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val keys : 'a t -> key BatEnum.t
    val values : 'a t -> 'a BatEnum.t
    val min_binding : 'a t -> key * 'a
    val min_binding_opt : 'a t -> (key * 'a) option
    val pop_min_binding : 'a t -> (key * 'a) * 'a t
    val max_binding : 'a t -> key * 'a
    val max_binding_opt : 'a t -> (key * 'a) option
    val pop_max_binding : 'a t -> (key * 'a) * 'a t
    val choose : 'a t -> key * 'a
    val choose_opt : 'a t -> (key * 'a) option
    val any : 'a t -> key * 'a
    val split : key -> 'a t -> 'a t * 'a option * 'a t
    val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
    val singleton : key -> 'a -> 'a t
    val bindings : 'a t -> (key * 'a) list
    val enum : 'a t -> (key * 'a) BatEnum.t
    val backwards : 'a t -> (key * 'a) BatEnum.t
    val of_enum : (key * 'a) BatEnum.t -> 'a t
    val for_all : (key -> 'a -> bool) -> 'a t -> bool
    val exists : (key -> 'a -> bool) -> 'a t -> bool
    val merge :
      (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
    val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
    val to_seq : 'a t -> (key * 'a) BatSeq.t
    val to_rev_seq : 'a t -> (key * 'a) BatSeq.t
    val to_seq_from : key -> 'a t -> (key * 'a) BatSeq.t
    val add_seq : (key * 'a) BatSeq.t -> 'a t -> 'a t
    val of_seq : (key * 'a) BatSeq.t -> 'a t
    val print :
      ?first:string ->
      ?last:string ->
      ?sep:string ->
      ?kvsep:string ->
      ('a BatInnerIO.output -> key -> unit) ->
      ('a BatInnerIO.output -> 'c -> unit) ->
      'a BatInnerIO.output -> 'c t -> unit
    module Exceptionless :
      sig
        val find : key -> 'a t -> 'a option
        val choose : 'a t -> (key * 'a) option
        val any : 'a t -> (key * 'a) option
      end
    module Infix :
      sig
        val ( --> ) : 'a t -> key -> 'a
        val ( <-- ) : 'a t -> key * 'a -> 'a t
      end
    module Labels :
      sig
        val add : key:key -> data:'a -> 'a t -> 'a t
        val iter : f:(key:key -> data:'a -> unit) -> 'a t -> unit
        val map : f:('a -> 'b) -> 'a t -> 'b t
        val mapi : f:(key:key -> data:'a -> 'b) -> 'a t -> 'b t
        val filterv : f:('a -> bool) -> 'a t -> 'a t
        val filter : f:(key -> 'a -> bool) -> 'a t -> 'a t
        val fold :
          f:(key:key -> data:'a -> 'b -> 'b) -> 'a t -> init:'b -> 'b
        val compare : cmp:('a -> 'a -> int) -> 'a t -> 'a t -> int
        val equal : cmp:('a -> 'a -> bool) -> 'a t -> 'a t -> bool
      end
  end
type 'value smap = 'value StringHashtbl.t
val smap_create : Z.t -> 'value smap
val smap_clear : 'value smap -> unit
val smap_add : 'value smap -> StringHashtbl.key -> 'value -> unit
val smap_of_list : (string * 'value) list -> 'value StringHashtbl.t
val smap_try_find : 'value smap -> StringHashtbl.key -> 'value option
val smap_fold :
  'value smap -> (StringHashtbl.key -> 'value -> 'a -> 'a) -> 'a -> 'a
val smap_remove : 'value smap -> StringHashtbl.key -> unit
val smap_keys : 'value smap -> StringHashtbl.key list
val smap_copy : 'value smap -> 'value StringHashtbl.t
val smap_size : 'value smap -> int
val smap_iter : 'value smap -> (StringHashtbl.key -> 'value -> unit) -> unit
exception PSMap_Found
type 'value psmap = 'value StringMap.t
val psmap_empty : unit -> 'value psmap
val psmap_add : 'value psmap -> string -> 'value -> 'value StringMap.t
val psmap_find_default : 'value psmap -> string -> 'value -> 'value
val psmap_try_find : 'value psmap -> string -> 'value option
val psmap_fold :
  'value psmap -> (StringMap.key -> 'value -> 'a -> 'a) -> 'a -> 'a
val psmap_find_map :
  'value psmap -> (StringMap.key -> 'value -> 'a option) -> 'a option
val psmap_modify :
  'value psmap -> string -> ('value option -> 'value) -> 'value StringMap.t
val psmap_merge : 'value psmap -> 'value psmap -> 'value psmap
module ZHashtbl :
  sig
    type key = Z.t
    type 'a t = 'a BatHashtbl.Make(Z).t
    val create : int -> 'a t
    val length : 'a t -> int
    val is_empty : 'a t -> bool
    val clear : 'a t -> unit
    val copy : 'a t -> 'a t
    val add : 'a t -> key -> 'a -> unit
    val remove : 'a t -> key -> unit
    val remove_all : 'a t -> key -> unit
    val find : 'a t -> key -> 'a
    val find_all : 'a t -> key -> 'a list
    val find_default : 'a t -> key -> 'a -> 'a
    val find_option : 'a t -> key -> 'a option
    val replace : 'a t -> key -> 'a -> unit
    val mem : 'a t -> key -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val for_all : (key -> 'a -> bool) -> 'a t -> bool
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val exists : (key -> 'a -> bool) -> 'a t -> bool
    val map : (key -> 'b -> 'c) -> 'b t -> 'c t
    val map_inplace : (key -> 'a -> 'a) -> 'a t -> unit
    val filter : ('a -> bool) -> 'a t -> 'a t
    val filter_inplace : ('a -> bool) -> 'a t -> unit
    val filteri : (key -> 'a -> bool) -> 'a t -> 'a t
    val filteri_inplace : (key -> 'a -> bool) -> 'a t -> unit
    val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t
    val filter_map_inplace : (key -> 'a -> 'a option) -> 'a t -> unit
    val modify : key -> ('a -> 'a) -> 'a t -> unit
    val modify_def : 'a -> key -> ('a -> 'a) -> 'a t -> unit
    val modify_opt : key -> ('a option -> 'a option) -> 'a t -> unit
    val merge :
      (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
    val merge_all :
      (key -> 'a list -> 'b list -> 'c list) -> 'a t -> 'b t -> 'c t
    val stats : 'a t -> BatHashtbl.statistics
    val keys : 'a t -> key BatEnum.t
    val values : 'a t -> 'a BatEnum.t
    val enum : 'a t -> (key * 'a) BatEnum.t
    val to_list : 'a t -> (key * 'a) list
    val of_enum : (key * 'a) BatEnum.t -> 'a t
    val of_list : (key * 'a) list -> 'a t
    val print :
      ?first:string ->
      ?last:string ->
      ?sep:string ->
      ('a BatInnerIO.output -> key -> unit) ->
      ('a BatInnerIO.output -> 'b -> unit) ->
      'a BatInnerIO.output -> 'b t -> unit
    module Exceptionless :
      sig
        val find : 'a t -> key -> 'a option
        val modify :
          key -> ('a -> 'a) -> 'a t -> (unit, exn) BatPervasives.result
      end
    module Infix :
      sig
        val ( --> ) : 'a t -> key -> 'a
        val ( <-- ) : 'a t -> key * 'a -> unit
      end
    module Labels :
      sig
        val add : 'a t -> key:key -> data:'a -> unit
        val replace : 'a t -> key:key -> data:'a -> unit
        val iter : f:(key:key -> data:'a -> unit) -> 'a t -> unit
        val for_all : f:(key:key -> data:'a -> bool) -> 'a t -> bool
        val map : f:(key:key -> data:'a -> 'b) -> 'a t -> 'b t
        val map_inplace : f:(key:key -> data:'a -> 'a) -> 'a t -> unit
        val filter : f:('a -> bool) -> 'a t -> 'a t
        val filter_inplace : f:('a -> bool) -> 'a t -> unit
        val filteri : f:(key:key -> data:'a -> bool) -> 'a t -> 'a t
        val filteri_inplace : f:(key:key -> data:'a -> bool) -> 'a t -> unit
        val filter_map : f:(key:key -> data:'a -> 'b option) -> 'a t -> 'b t
        val filter_map_inplace :
          f:(key:key -> data:'a -> 'a option) -> 'a t -> unit
        val fold :
          f:(key:key -> data:'a -> 'b -> 'b) -> 'a t -> init:'b -> 'b
        val exists : f:(key:key -> data:'a -> bool) -> 'a t -> bool
        val modify : key:key -> f:('a -> 'a) -> 'a t -> unit
        val modify_def :
          default:'a -> key:key -> f:('a -> 'a) -> 'a t -> unit
        val modify_opt :
          key:key -> f:('a option -> 'a option) -> 'a t -> unit
        val merge :
          f:(key -> 'a option -> 'b option -> 'c option) ->
          left:'a t -> right:'b t -> 'c t
        val merge_all :
          f:(key -> 'a list -> 'b list -> 'c list) ->
          left:'a t -> right:'b t -> 'c t
      end
  end
module ZMap :
  sig
    type key = Z.t
    type 'a t = 'a BatMap.Make(Z).t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val cardinal : 'a t -> int
    val add : key -> 'a -> 'a t -> 'a t
    val update_stdlib : key -> ('a option -> 'a option) -> 'a t -> 'a t
    val update : key -> key -> 'a -> 'a t -> 'a t
    val find : key -> 'a t -> 'a
    val find_opt : key -> 'a t -> 'a option
    val find_default : 'a -> key -> 'a t -> 'a
    val find_first : (key -> bool) -> 'a t -> key * 'a
    val find_first_opt : (key -> bool) -> 'a t -> (key * 'a) option
    val find_last : (key -> bool) -> 'a t -> key * 'a
    val find_last_opt : (key -> bool) -> 'a t -> (key * 'a) option
    val remove : key -> 'a t -> 'a t
    val remove_exn : key -> 'a t -> 'a t
    val modify : key -> ('a -> 'a) -> 'a t -> 'a t
    val modify_def : 'a -> key -> ('a -> 'a) -> 'a t -> 'a t
    val modify_opt : key -> ('a option -> 'a option) -> 'a t -> 'a t
    val extract : key -> 'a t -> 'a * 'a t
    val pop : 'a t -> (key * 'a) * 'a t
    val mem : key -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val filterv : ('a -> bool) -> 'a t -> 'a t
    val filter : (key -> 'a -> bool) -> 'a t -> 'a t
    val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val keys : 'a t -> key BatEnum.t
    val values : 'a t -> 'a BatEnum.t
    val min_binding : 'a t -> key * 'a
    val min_binding_opt : 'a t -> (key * 'a) option
    val pop_min_binding : 'a t -> (key * 'a) * 'a t
    val max_binding : 'a t -> key * 'a
    val max_binding_opt : 'a t -> (key * 'a) option
    val pop_max_binding : 'a t -> (key * 'a) * 'a t
    val choose : 'a t -> key * 'a
    val choose_opt : 'a t -> (key * 'a) option
    val any : 'a t -> key * 'a
    val split : key -> 'a t -> 'a t * 'a option * 'a t
    val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
    val singleton : key -> 'a -> 'a t
    val bindings : 'a t -> (key * 'a) list
    val enum : 'a t -> (key * 'a) BatEnum.t
    val backwards : 'a t -> (key * 'a) BatEnum.t
    val of_enum : (key * 'a) BatEnum.t -> 'a t
    val for_all : (key -> 'a -> bool) -> 'a t -> bool
    val exists : (key -> 'a -> bool) -> 'a t -> bool
    val merge :
      (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
    val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
    val to_seq : 'a t -> (key * 'a) BatSeq.t
    val to_rev_seq : 'a t -> (key * 'a) BatSeq.t
    val to_seq_from : key -> 'a t -> (key * 'a) BatSeq.t
    val add_seq : (key * 'a) BatSeq.t -> 'a t -> 'a t
    val of_seq : (key * 'a) BatSeq.t -> 'a t
    val print :
      ?first:string ->
      ?last:string ->
      ?sep:string ->
      ?kvsep:string ->
      ('a BatInnerIO.output -> key -> unit) ->
      ('a BatInnerIO.output -> 'c -> unit) ->
      'a BatInnerIO.output -> 'c t -> unit
    module Exceptionless :
      sig
        val find : key -> 'a t -> 'a option
        val choose : 'a t -> (key * 'a) option
        val any : 'a t -> (key * 'a) option
      end
    module Infix :
      sig
        val ( --> ) : 'a t -> key -> 'a
        val ( <-- ) : 'a t -> key * 'a -> 'a t
      end
    module Labels :
      sig
        val add : key:key -> data:'a -> 'a t -> 'a t
        val iter : f:(key:key -> data:'a -> unit) -> 'a t -> unit
        val map : f:('a -> 'b) -> 'a t -> 'b t
        val mapi : f:(key:key -> data:'a -> 'b) -> 'a t -> 'b t
        val filterv : f:('a -> bool) -> 'a t -> 'a t
        val filter : f:(key -> 'a -> bool) -> 'a t -> 'a t
        val fold :
          f:(key:key -> data:'a -> 'b -> 'b) -> 'a t -> init:'b -> 'b
        val compare : cmp:('a -> 'a -> int) -> 'a t -> 'a t -> int
        val equal : cmp:('a -> 'a -> bool) -> 'a t -> 'a t -> bool
      end
  end
type 'value imap = 'value ZHashtbl.t
val imap_create : Z.t -> 'value imap
val imap_clear : 'value imap -> unit
val imap_add : 'value imap -> ZHashtbl.key -> 'value -> unit
val imap_of_list : (Z.t * 'value) list -> 'value ZHashtbl.t
val imap_try_find : 'value imap -> ZHashtbl.key -> 'value option
val imap_fold :
  'value imap -> (ZHashtbl.key -> 'value -> 'a -> 'a) -> 'a -> 'a
val imap_remove : 'value imap -> ZHashtbl.key -> unit
val imap_keys : 'value imap -> ZHashtbl.key list
val imap_copy : 'value imap -> 'value ZHashtbl.t
type 'value pimap = 'value ZMap.t
val pimap_empty : unit -> 'value pimap
val pimap_add : 'value pimap -> Z.t -> 'value -> 'value ZMap.t
val pimap_find_default : 'value pimap -> Z.t -> 'value -> 'value
val pimap_try_find : 'value pimap -> Z.t -> 'value option
val pimap_fold : 'value pimap -> (ZMap.key -> 'value -> 'a -> 'a) -> 'a -> 'a
val batstring_nsplit : string -> string -> string list
val format : string -> string list -> string
val format1 : string -> string -> string
val format2 : string -> string -> string -> string
val format3 : string -> string -> string -> string -> string
val format4 : string -> string -> string -> string -> string -> string
val format5 :
  string -> string -> string -> string -> string -> string -> string
val format6 :
  string ->
  string -> string -> string -> string -> string -> string -> string
val flush_stdout : unit -> unit
val stdout_isatty : unit -> bool option
val colorize : string -> string * string -> string
val colorize_bold : string -> string
val colorize_red : string -> string
val colorize_cyan : string -> string
val pr : ('a, out_channel, unit) format -> 'a
val spr : ('a, unit, string) format -> 'a
val fpr : out_channel -> ('a, out_channel, unit) format -> 'a
type json =
    JsonNull
  | JsonBool of bool
  | JsonInt of Z.t
  | JsonStr of string
  | JsonList of json list
  | JsonAssoc of (string * json) list
type printer = {
  printer_prinfo : string -> unit;
  printer_prwarning : string -> unit;
  printer_prerror : string -> unit;
  printer_prgeneric : string -> (unit -> string) -> (unit -> json) -> unit;
}
val default_printer : printer
val current_printer : printer ref
val set_printer : printer -> unit
val print_raw : string -> unit
val print_string : string -> unit
val print_generic : string -> ('a -> string) -> ('a -> json) -> 'a -> unit
val print_any : 'a -> unit
val strcat : string -> string -> string
val concat_l : string -> string list -> string
val string_of_unicode : int array -> string
val unicode_of_string : string -> int array
val base64_encode : string -> string
val base64_decode : string -> string
val char_of_int : Z.t -> int
val int_of_string : string -> Z.t
val safe_int_of_string : string -> Z.t option
val int_of_char : int -> Z.t
val int_of_byte : 'a -> 'a
val int_of_uint8 : char -> Z.t
val uint16_of_int : Z.t -> int
val byte_of_char : 'a -> 'a
val float_of_string : string -> float
val float_of_byte : char -> float
val float_of_int32 : int -> float
val float_of_int64 : int64 -> float
val int_of_int32 : 'a -> 'a
val int32_of_int : int -> int32
val string_of_int : Z.t -> string
val string_of_bool : bool -> string
val string_of_int32 : int32 -> string
val string_of_int64 : int64 -> string
val string_of_float : float -> string
val string_of_char : int -> BatUTF8.t
val hex_string_of_byte : int -> string
val string_of_bytes : int array -> string
val bytes_of_string : string -> int array
val starts_with : string -> string -> bool
val trim_string : string -> string
val ends_with : string -> string -> bool
val char_at : BatUTF8.t -> Z.t -> int
val is_upper : int -> bool
val contains : string -> string -> bool
val substring_from : string -> Z.t -> string
val substring : string -> Z.t -> Z.t -> string
val replace_char : string -> int -> int -> BatUTF8.t
val replace_chars : string -> int -> string -> string
val hashcode : StringOps.t -> Z.t
val compare : BatString.t -> BatString.t -> Z.t
val split : string -> string -> string list
val splitlines : string -> string list
val iof : float -> int
val foi : int -> float
val print1 : string -> string -> unit
val print2 : string -> string -> string -> unit
val print3 : string -> string -> string -> string -> unit
val print4 : string -> string -> string -> string -> string -> unit
val print5 : string -> string -> string -> string -> string -> string -> unit
val print6 :
  string -> string -> string -> string -> string -> string -> string -> unit
val print : string -> string list -> unit
val print_error : string -> unit
val print1_error : string -> string -> unit
val print2_error : string -> string -> string -> unit
val print3_error : string -> string -> string -> string -> unit
val print_warning : string -> unit
val print1_warning : string -> string -> unit
val print2_warning : string -> string -> string -> unit
val print3_warning : string -> string -> string -> string -> unit
val stderr : out_channel
val stdout : out_channel
val fprint : out_channel -> string -> string list -> unit
val is_left : ('a, 'b) FStar_Pervasives.either -> bool
val is_right : ('a, 'b) FStar_Pervasives.either -> bool
val left : ('a, 'b) FStar_Pervasives.either -> 'a
val right : ('a, 'b) FStar_Pervasives.either -> 'b
val ( -<- ) : ('a -> 'b) -> ('c -> 'a) -> 'c -> 'b
val find_dup : ('a -> 'a -> bool) -> 'a list -> 'a option
val nodups : ('a -> 'a -> bool) -> 'a list -> bool
val remove_dups : ('a -> 'a -> bool) -> 'a list -> 'a list
val is_none : 'a option -> bool
val is_some : 'a option -> bool
val must : 'a option -> 'a
val dflt : 'a -> 'a option -> 'a
val find_opt : ('a -> bool) -> 'a list -> 'a option
val sort_with : ('a -> 'a -> Z.t) -> 'a list -> 'a list
val bind_opt : 'a option -> ('a -> 'b option) -> 'b option
val catch_opt : 'a option -> (unit -> 'a option) -> 'a option
val map_opt : 'a option -> ('a -> 'b) -> 'b option
val iter_opt : 'a option -> ('a -> 'b) -> unit
val find_map : 'a list -> ('a -> 'b option) -> 'b option
val try_find : ('a -> bool) -> 'a list -> 'a option
val try_find_index : ('a -> bool) -> 'a list -> Z.t option
val fold_map : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list
val choose_map :
  ('a -> 'b -> 'a * 'c option) -> 'a -> 'b list -> 'a * 'c list
val for_all : ('a -> bool) -> 'a list -> bool
val for_some : ('a -> bool) -> 'a list -> bool
val forall_exists : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
val multiset_equiv : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
val take : ('a -> bool) -> 'a list -> 'a list * 'a list
val fold_flatten : ('a -> 'b -> 'a * 'b list) -> 'a -> 'b list -> 'a
val add_unique : ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list
val first_N : Z.t -> 'a list -> 'a list * 'a list
val nth_tail : Z.t -> 'a list -> 'a list
val prefix : 'a list -> 'a list * 'a
val prefix_until : ('a -> bool) -> 'a list -> ('a list * 'a * 'a list) option
val string_to_ascii_bytes : string -> char array
val ascii_bytes_to_string : char array -> string
val mk_ref : 'a -> 'a ref
type ('s, 'a) state = 's -> 'a * 's
val get : ('s, 's) state
val upd : ('s -> 's) -> ('s, unit) state
val put : 's -> ('s, unit) state
val ret : 'a -> ('s, 'a) state
val bind : ('s, 'a) state -> ('a -> ('s, 'b) state) -> ('s, 'b) state
val ( >> ) : ('a, 'b) state -> ('b -> ('a, 'c) state) -> ('a, 'c) state
val run_st : 's -> ('s, 'a) state -> 'a * 's
val stmap : 'a list -> ('a -> ('s, 'b) state) -> ('s, 'b list) state
val stmapi : 'a list -> (int -> 'a -> ('s, 'b) state) -> ('s, 'b list) state
val stiter : 'a list -> ('a -> ('s, unit) state) -> ('s, unit) state
val stfoldr_pfx :
  'a list -> ('a list -> 'a -> ('s, unit) state) -> ('s, unit) state
val stfold : 'b -> 'a list -> ('b -> 'a -> ('s, 'b) state) -> ('s, 'b) state
type file_handle = out_channel
val open_file_for_writing : string -> file_handle
val append_to_file : file_handle -> string -> unit
val close_file : file_handle -> unit
val write_file : string -> string -> unit
val copy_file : string -> string -> unit
val flush_file : file_handle -> unit
val delete_file : string -> unit
val file_get_contents : string -> string
val file_get_lines : string -> string list
val concat_dir_filename : string -> string -> string
val mkdir : bool -> string -> unit
val for_range : Z.t -> Z.t -> (Z.t -> unit) -> unit
val incr : Z.t ref -> unit
val decr : Z.t ref -> unit
val geq : int -> int -> bool
val get_exec_dir : unit -> string
val expand_environment_variable : string -> string option
val physical_equality : 'a -> 'a -> bool
val check_sharing : 'a -> 'a -> string -> unit
type oWriter = {
  write_byte : char -> unit;
  write_bool : bool -> unit;
  write_int : int -> unit;
  write_int32 : int32 -> unit;
  write_int64 : int64 -> unit;
  write_char : char -> unit;
  write_double : float -> unit;
  write_bytearray : char array -> unit;
  write_string : string -> unit;
  close : unit -> unit;
}
type oReader = {
  read_byte : unit -> char;
  read_bool : unit -> bool;
  read_int : unit -> int;
  read_int32 : unit -> int32;
  read_int64 : unit -> int64;
  read_char : unit -> char;
  read_double : unit -> float;
  read_bytearray : unit -> char array;
  read_string : unit -> string;
  close : unit -> unit;
}
module MkoReader :
  sig
    val read_byte : oReader -> unit -> char
    val read_bool : oReader -> unit -> bool
    val read_int : oReader -> unit -> int32
    val read_int32 : oReader -> unit -> int32
    val read_int64 : oReader -> unit -> int64
    val read_char : oReader -> unit -> char
    val read_double : oReader -> unit -> float
    val read_bytearray : oReader -> unit -> char array
    val read_string : oReader -> unit -> string
    val close : oReader -> unit -> unit
  end
module MkoWriter :
  sig
    val write_byte : oWriter -> char -> unit
    val write_bool : oWriter -> bool -> unit
    val write_int : oWriter -> int32 -> unit
    val write_int32 : oWriter -> int32 -> unit
    val write_int64 : oWriter -> int64 -> unit
    val write_char : oWriter -> char -> unit
    val write_double : oWriter -> float -> unit
    val write_bytearray : oWriter -> char array -> unit
    val write_string : oWriter -> string -> unit
    val close : oReader -> unit -> unit
  end
val get_owriter : string -> oWriter
val get_oreader : string -> oReader
val getcwd : unit -> string
val readdir : string -> string list
val paths_to_same_file : string -> string -> bool
val file_exists : string -> bool
val is_directory : string -> bool
val basename : string -> string
val dirname : string -> string
val print_endline : string -> unit
val map_option : ('a -> 'b) -> 'a option -> 'b option
val save_value_to_file : string -> 'a -> unit
val load_value_from_file : string -> 'a option
val save_2values_to_file : string -> 'a -> 'b -> unit
val load_2values_from_file : string -> ('a * 'b) option
val print_exn : exn -> string
val digest_of_file : string -> BatDigest.t
val digest_of_string : string -> string
val touch_file : string -> unit
val ensure_decimal : string -> string
val measure_execution_time : string -> (unit -> 'a) -> 'a
val return_execution_time : (unit -> 'a) -> 'a * float
type hint = {
  hint_name : string;
  hint_index : Z.t;
  fuel : Z.t;
  ifuel : Z.t;
  unsat_core : string list option;
  query_elapsed_time : Z.t;
  hash : string option;
}
type hints = hint option list
type hints_db = { module_digest : string; hints : hints; }
type hints_read_result = HintsOK of hints_db | MalformedJson | UnableToOpen
val write_hints : string -> hints_db -> unit
val read_hints : string -> hints_read_result
exception UnsupportedJson
val json_of_yojson :
  ([> `Assoc of (string * 'a) list
    | `Bool of bool
    | `Int of int
    | `List of 'a list
    | `Null
    | `String of string ]
   as 'a) ->
  json option
val yojson_of_json :
  json ->
  ([> `Assoc of (string * 'a) list
    | `Bool of bool
    | `Int of int
    | `List of 'a list
    | `Null
    | `String of string ]
   as 'a)
val json_of_string : string -> json option
val string_of_json : json -> string
type 'a ref = 'a FStar_Monotonic_Heap.ref
val read : 'a Stdlib.ref -> 'a
val write : 'a Stdlib.ref -> 'a -> unit
val ( ! ) : 'a Stdlib.ref -> 'a
val ( := ) : 'a Stdlib.ref -> 'a -> unit
val marshal : 'a -> string
val unmarshal : string -> 'a
type signedness = Unsigned | Signed
type width = Int8 | Int16 | Int32 | Int64
val z_pow2 : Z.t -> Z.t
val bounds : signedness -> width -> Z.t * Z.t
val within_bounds : string -> signedness -> width -> bool
val print_array : ('a -> string) -> 'a array -> string
val array_of_list : 'a list -> 'a array
val array_length : 'a FStar_ImmutableArray_Base.t -> Z.t
val array_index : 'a FStar_ImmutableArray_Base.t -> Z.t -> 'a

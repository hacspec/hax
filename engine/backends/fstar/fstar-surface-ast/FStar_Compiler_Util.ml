let ensure_decimal s = Z.to_string (Z.of_string s)


let max_int = Z.of_int max_int
let is_letter c = if c > 255 then false else BatChar.is_letter (BatChar.chr c)
let is_digit  c = if c > 255 then false else BatChar.is_digit  (BatChar.chr c)
let is_letter_or_digit c = is_letter c || is_digit c
let is_symbol c = if c > 255 then false else BatChar.is_symbol (BatChar.chr c)

(* Modeled after: Char.IsPunctuation in .NET
   (http://www.dotnetperls.com/char-ispunctuation)
*)
let is_punctuation c = List.mem c [33; 34; 35; 37; 38; 39; 40; 41; 42; 44; 45; 46; 47; 58; 59; 63; 64; 91; 92; 93; 95; 123; 125]
(*'!','"','#','%','&','\'','(',')','*',',','-','.','/',':',';','?','@','[','\\',']','_','{','}'*)

let return_all x = x

let get_file_last_modification_time f = (BatUnix.stat f).BatUnix.st_mtime
let is_before t1 t2 = compare t1 t2 < 0
let string_of_time = string_of_float

exception Impos

let cur_sigint_handler : Sys.signal_behavior ref =
  ref Sys.Signal_default

exception SigInt
type sigint_handler = Sys.signal_behavior

let sigint_ignore: sigint_handler =
  Sys.Signal_ignore

let sigint_delay = ref 0
let sigint_pending = ref false

let raise_sigint _ =
  sigint_pending := false;
  raise SigInt

let raise_sigint_maybe_delay _ =
  (* This function should not do anything complicated, lest it cause deadlocks.
   * Calling print_string, for example, can cause a deadlock (print_string →
   * caml_flush → process_pending_signals → caml_execute_signal → raise_sigint →
   * print_string → caml_io_mutex_lock ⇒ deadlock) *)
  if !sigint_delay = 0
  then raise_sigint ()
  else sigint_pending := true

let sigint_raise: sigint_handler =
  Sys.Signal_handle raise_sigint_maybe_delay

let set_sigint_handler sigint_handler =
  cur_sigint_handler := sigint_handler;
  Sys.set_signal Sys.sigint !cur_sigint_handler

let with_sigint_handler handler f =
  let original_handler = !cur_sigint_handler in
  BatPervasives.finally
    (fun () -> Sys.set_signal Sys.sigint original_handler)
    (fun () -> set_sigint_handler handler; f ())
    ()

let get_file_extension (fn:string) : string = snd (BatString.rsplit fn ".")
let is_path_absolute path_str =
  let open Batteries.Incubator in
  let open BatPathGen.OfString in
  let path_str' = of_string path_str in
  is_absolute path_str'
let join_paths path_str0 path_str1 =
  let open Batteries.Incubator in
  let open BatPathGen.OfString in
  let open BatPathGen.OfString.Operators in
  to_string ((of_string path_str0) //@ (of_string path_str1))

let normalize_file_path (path_str:string) =
  let open Batteries.Incubator in
  let open BatPathGen.OfString in
  let open BatPathGen.OfString.Operators in
  to_string
    (normalize_in_tree
       (let path = of_string path_str in
         if is_absolute path then
           path
         else
           let pwd = of_string (BatSys.getcwd ()) in
           pwd //@ path))

type stream_reader = BatIO.input
let open_stdin () = BatIO.stdin
let read_line s =
  try
    Some (BatIO.read_line s)
  with
    _ -> None
let nread (s:stream_reader) (n:Z.t) =
  try
    Some (BatIO.nread s (Z.to_int n))
  with
    _ -> None

let poll_stdin (f:float) =
    try 
      let ready_fds, _, _ = Unix.select [Unix.stdin] [] [] f in
      match ready_fds with
      | [] -> false
      | _ -> true
    with
    | _ -> false

type string_builder = BatBuffer.t
let new_string_builder () = BatBuffer.create 256
let clear_string_builder b = BatBuffer.clear b
let string_of_string_builder b = BatBuffer.contents b
let string_builder_append b s = BatBuffer.add_string b s

let message_of_exn (e:exn) = Printexc.to_string e
let trace_of_exn (e:exn) = Printexc.get_backtrace ()

type 'a set = ('a list) * ('a -> 'a -> bool)
[@@deriving show]
let set_to_yojson _ _ = `Null
let set_of_yojson _ _ = failwith "cannot readback"

let set_is_empty ((s, _):'a set) =
  match s with
  | [] -> true
  | _ -> false

let as_set (l:'a list) (cmp:('a -> 'a -> Z.t)) = (l, fun x y -> cmp x y = Z.zero)
let new_set (cmp:'a -> 'a -> Z.t) : 'a set = as_set [] cmp

let set_elements ((s1, eq):'a set) : 'a list =
  let rec aux out = function
    | [] -> BatList.rev_append out []
    | hd::tl ->
       if BatList.exists (eq hd) out then
         aux out tl
       else
         aux (hd::out) tl in
  aux [] s1

let set_add a ((s, b):'a set) = (s@[a], b)
let set_remove x ((s1, eq):'a set) =
  (BatList.filter (fun y -> not (eq x y)) s1, eq)
let set_mem a ((s, b):'a set) = BatList.exists (b a) s
let set_union ((s1, b):'a set) ((s2, _):'a set) = (s1@s2, b)
let set_intersect ((s1, eq):'a set) ((s2, _):'a set) =
  (BatList.filter (fun y -> BatList.exists (eq y) s2) s1, eq)
let set_is_subset_of ((s1, eq):'a set) ((s2, _):'a set) =
  BatList.for_all (fun y -> BatList.exists (eq y) s2) s1
let set_count ((s1, _):'a set) = Z.of_int (BatList.length s1)
let set_difference ((s1, eq):'a set) ((s2, _):'a set) : 'a set =
  (BatList.filter (fun y -> not (BatList.exists (eq y) s2)) s1, eq)
let set_symmetric_difference ((s1, eq):'a set) ((s2, _):'a set) : 'a set =
  set_union (set_difference (s1, eq) (s2, eq))
            (set_difference (s2, eq) (s1, eq))
let set_eq ((s1, eq):'a set) ((s2, _):'a set) : bool =
  set_is_empty (set_symmetric_difference (s1, eq) (s2, eq))

(* module StringOps = *)
(*   struct *)
(*     type t = string *)
(*     let equal (x:t) (y:t) = x=y *)
(*     let compare (x:t) (y:t) = BatString.compare x y *)
(*     let hash (x:t) = BatHashtbl.hash x *)
(*   end *)

(* module StringHashtbl = BatHashtbl.Make(StringOps) *)
(* module StringMap = BatMap.Make(StringOps) *)

(* type 'value smap = 'value StringHashtbl.t *)
(* let smap_create (i:Z.t) : 'value smap = StringHashtbl.create (Z.to_int i) *)
(* let smap_clear (s:('value smap)) = StringHashtbl.clear s *)
(* let smap_add (m:'value smap) k (v:'value) = StringHashtbl.replace m k v *)
(* let smap_of_list (l: (string * 'value) list) = *)
(*   let s = StringHashtbl.create (BatList.length l) in *)
(*   FStar_List.iter (fun (x,y) -> smap_add s x y) l; *)
(*   s *)
(* let smap_try_find (m:'value smap) k = StringHashtbl.find_option m k *)
(* let smap_fold (m:'value smap) f a = StringHashtbl.fold f m a *)
(* let smap_remove (m:'value smap) k = StringHashtbl.remove m k *)
(* let smap_keys (m:'value smap) = smap_fold m (fun k _ acc -> k::acc) [] *)
(* let smap_copy (m:'value smap) = StringHashtbl.copy m *)
(* let smap_size (m:'value smap) = StringHashtbl.length m *)
(* let smap_iter (m:'value smap) f = StringHashtbl.iter f m *)

(* exception PSMap_Found *)
(* type 'value psmap = 'value StringMap.t *)
(* let psmap_empty (_: unit) : 'value psmap = StringMap.empty *)
(* let psmap_add (map: 'value psmap) (key: string) (value: 'value) = StringMap.add key value map *)
(* let psmap_find_default (map: 'value psmap) (key: string) (dflt: 'value) = *)
(*   StringMap.find_default dflt key map *)
(* let psmap_try_find (map: 'value psmap) (key: string) = *)
(*   StringMap.Exceptionless.find key map *)
(* let psmap_fold (m:'value psmap) f a = StringMap.fold f m a *)
(* let psmap_find_map (m:'value psmap) f = *)
(*   let res = ref None in *)
(*   let upd k v = *)
(*     let r = f k v in *)
(*     if r <> None then (res := r; raise PSMap_Found) in *)
(*   (try StringMap.iter upd m with PSMap_Found -> ()); *)
(*   !res *)
(* let psmap_modify (m: 'value psmap) (k: string) (upd: 'value option -> 'value) = *)
(*   StringMap.modify_opt k (fun vopt -> Some (upd vopt)) m *)

(* let psmap_merge (m1: 'value psmap) (m2: 'value psmap) : 'value psmap = *)
(*   psmap_fold m1 (fun k v m -> psmap_add m k v) m2 *)

(* module ZHashtbl = BatHashtbl.Make(Z) *)
(* module ZMap = BatMap.Make(Z) *)

(* type 'value imap = 'value ZHashtbl.t *)
(* let imap_create (i:Z.t) : 'value imap = ZHashtbl.create (Z.to_int i) *)
(* let imap_clear (s:('value imap)) = ZHashtbl.clear s *)
(* let imap_add (m:'value imap) k (v:'value) = ZHashtbl.replace m k v *)
(* let imap_of_list (l: (Z.t * 'value) list) = *)
(*   let s = ZHashtbl.create (BatList.length l) in *)
(*   FStar_List.iter (fun (x,y) -> imap_add s x y) l; *)
(*   s *)
(* let imap_try_find (m:'value imap) k = ZHashtbl.find_option m k *)
(* let imap_fold (m:'value imap) f a = ZHashtbl.fold f m a *)
(* let imap_remove (m:'value imap) k = ZHashtbl.remove m k *)
(* let imap_keys (m:'value imap) = imap_fold m (fun k _ acc -> k::acc) [] *)
(* let imap_copy (m:'value imap) = ZHashtbl.copy m *)

(* type 'value pimap = 'value ZMap.t *)
(* let pimap_empty (_: unit) : 'value pimap = ZMap.empty *)
(* let pimap_add (map: 'value pimap) (key: Z.t) (value: 'value) = ZMap.add key value map *)
(* let pimap_find_default (map: 'value pimap) (key: Z.t) (dflt: 'value) = *)
(*   ZMap.find_default dflt key map *)
(* let pimap_try_find (map: 'value pimap) (key: Z.t) = *)
(*   ZMap.Exceptionless.find key map *)
(* let pimap_fold (m:'value pimap) f a = ZMap.fold f m a *)

(* restore pre-2.11 BatString.nsplit behavior,
   see https://github.com/ocaml-batteries-team/batteries-included/issues/845 *)
let batstring_nsplit s t =
  if s = "" then [] else BatString.split_on_string t s

let format (fmt:string) (args:string list) =
  let frags = batstring_nsplit fmt "%s" in
  if BatList.length frags <> BatList.length args + 1 then
    failwith ("Not enough arguments to format string " ^fmt^ " : expected " ^ (Stdlib.string_of_int (BatList.length frags)) ^ " got [" ^ (BatString.concat ", " args) ^ "] frags are [" ^ (BatString.concat ", " frags) ^ "]")
  else
    let args = args@[""] in
    BatList.fold_left2 (fun out frag arg -> out ^ frag ^ arg) "" frags args

let format1 f a = format f [a]
let format2 f a b = format f [a;b]
let format3 f a b c = format f [a;b;c]
let format4 f a b c d = format f [a;b;c;d]
let format5 f a b c d e = format f [a;b;c;d;e]
let format6 f a b c d e g = format f [a;b;c;d;e;g]

let flush_stdout () = flush stdout

let stdout_isatty () = Some (Unix.isatty Unix.stdout)

let colorize s colors =
  match colors with
  | (c1,c2) ->
     match stdout_isatty () with
     | Some true -> format3 "%s%s%s" c1 s c2
     | _ -> s

let colorize_bold s =
  match stdout_isatty () with
  | Some true -> format3 "%s%s%s" "\x1b[39;1m" s "\x1b[0m"
  | _ -> s

let colorize_red s =
  match stdout_isatty () with
  | Some true -> format3 "%s%s%s" "\x1b[31;1m" s "\x1b[0m"
  | _ -> s

let colorize_cyan s =
  match stdout_isatty () with
  | Some true -> format3 "%s%s%s" "\x1b[36;1m" s "\x1b[0m"
  | _ -> s

let pr  = Printf.printf
let spr = Printf.sprintf
let fpr = Printf.fprintf

type json =
| JsonNull
| JsonBool of bool
| JsonInt of Z.t
| JsonStr of string
| JsonList of json list
| JsonAssoc of (string * json) list

type printer = {
  printer_prinfo: string -> unit;
  printer_prwarning: string -> unit;
  printer_prerror: string -> unit;
  printer_prgeneric: string -> (unit -> string) -> (unit -> json) -> unit
}

let default_printer =
  { printer_prinfo = (fun s -> pr "%s" s; flush stdout);
    printer_prwarning = (fun s -> fpr stderr "%s" (colorize_cyan s); flush stdout; flush stderr);
    printer_prerror = (fun s -> fpr stderr "%s" (colorize_red s); flush stdout; flush stderr);
    printer_prgeneric = fun label get_string get_json -> pr "%s: %s" label (get_string ())}

let current_printer = ref default_printer
let set_printer printer = current_printer := printer

let print_raw s = set_binary_mode_out stdout true; pr "%s" s; flush stdout
let print_string s = (!current_printer).printer_prinfo s
let print_generic label to_string to_json a = (!current_printer).printer_prgeneric label (fun () -> to_string a) (fun () -> to_json a)
let print_any s = (!current_printer).printer_prinfo (Marshal.to_string s [])
let strcat s1 s2 = s1 ^ s2
let concat_l sep (l:string list) = BatString.concat sep l

let string_of_unicode (bytes:int array) =
  BatArray.fold_left (fun acc b -> acc^(BatUTF8.init 1 (fun _ -> BatUChar.of_int b))) "" bytes
let unicode_of_string (string:string) =
  let n = BatUTF8.length string in
  let t = Array.make n 0 in
  let i = ref 0 in
  BatUTF8.iter (fun c -> t.(!i) <- BatUChar.code c; incr i) string;
  t
let base64_encode s = BatBase64.str_encode s
let base64_decode s = BatBase64.str_decode s
let char_of_int i = Z.to_int i
let int_of_string = Z.of_string
let safe_int_of_string x = try Some (int_of_string x) with Invalid_argument _ -> None
let int_of_char x = Z.of_int x
let int_of_byte x = x
let int_of_uint8 x = Z.of_int (Char.code x)
let uint16_of_int i = Z.to_int i
let byte_of_char c = c

let float_of_string s = float_of_string s
let float_of_byte b = float_of_int (Char.code b)
let float_of_int32 = float_of_int
let float_of_int64 = BatInt64.to_float

let int_of_int32 i = i
let int32_of_int i = BatInt32.of_int i

let string_of_int = Z.to_string
let string_of_bool = string_of_bool
let string_of_int32 = BatInt32.to_string
let string_of_int64 = BatInt64.to_string
let string_of_float = string_of_float
let string_of_char i = BatUTF8.init 1 (fun _ -> BatUChar.chr i)
let hex_string_of_byte (i:int) =
  let hs = spr "%x" i in
  if (String.length hs = 1) then "0" ^ hs
  else hs
let string_of_bytes = string_of_unicode
let bytes_of_string = unicode_of_string
let starts_with = BatString.starts_with
let trim_string = BatString.trim
let ends_with = BatString.ends_with
let char_at s index = BatUChar.code (BatUTF8.get s (Z.to_int index))
let is_upper c = 65 <= c && c <= 90
let contains (s1:string) (s2:string) = BatString.exists s1 s2
let substring_from s index = BatString.tail s (Z.to_int index)
let substring s i j = BatString.sub s (Z.to_int i) (Z.to_int j)
let replace_char (s:string) c1 c2 =
  let c1, c2 = BatUChar.chr c1, BatUChar.chr c2 in
  BatUTF8.map (fun x -> if x = c1 then c2 else x) s
let replace_chars (s:string) c (by:string) =
  BatString.replace_chars (fun x -> if x = Char.chr c then by else BatString.of_char x) s
(* let hashcode s = Z.of_int (StringOps.hash s) *)
let compare s1 s2 = Z.of_int (BatString.compare s1 s2)
let split s sep = BatString.split_on_string sep s
let splitlines s = split s "\n"

let iof = int_of_float
let foi = float_of_int

let print1 a b = print_string (format1 a b)
let print2 a b c = print_string (format2 a b c)
let print3 a b c d = print_string (format3 a b c d)
let print4 a b c d e = print_string (format4 a b c d e)
let print5 a b c d e f = print_string (format5 a b c d e f)
let print6 a b c d e f g = print_string (format6 a b c d e f g)
let print fmt args = print_string (format fmt args)

let print_error s = (!current_printer).printer_prerror s
let print1_error a b = print_error (format1 a b)
let print2_error a b c = print_error (format2 a b c)
let print3_error a b c d = print_error (format3 a b c d)

let print_warning s = (!current_printer).printer_prwarning s
let print1_warning a b = print_warning (format1 a b)
let print2_warning a b c = print_warning (format2 a b c)
let print3_warning a b c d = print_warning (format3 a b c d)

let stderr = stderr
let stdout = stdout

let fprint oc fmt args = Printf.fprintf oc "%s" (format fmt args)

[@@deriving yojson,show]

let is_left = function
  | FStar_Pervasives.Inl _ -> true
  | _ -> false

let is_right = function
  | FStar_Pervasives.Inr _ -> true
  | _ -> false

let left = function
  | FStar_Pervasives.Inl x -> x
  | _ -> failwith "Not in left"
let right = function
  | FStar_Pervasives.Inr x -> x
  | _ -> failwith "Not in right"

let (-<-) f g x = f (g x)

let find_dup f l =
  let rec aux = function
    | hd::tl ->
       let hds, tl' = BatList.partition (f hd) tl in
       (match hds with
        | [] -> aux tl'
        | _ -> Some hd)
    | _ -> None in
  aux l

let nodups f l = match find_dup f l with | None -> true | _ -> false

let remove_dups f l =
  let rec aux out = function
    | hd::tl -> let _, tl' = BatList.partition (f hd) tl in aux (hd::out) tl'
    | _ -> out in
  aux [] l

let must = function
  | Some x -> x
  | None -> failwith "Empty option"

let dflt x = function
  | None   -> x
  | Some x -> x

let bind_opt opt f =
  match opt with
  | None -> None
  | Some x -> f x

let map_opt opt f =
  match opt with
  | None -> None
  | Some x -> Some (f x)

let try_find f l = BatList.find_opt f l

let for_all f l = BatList.for_all f l
let for_some f l = BatList.exists f l

let first_N n l =
  let n = Z.to_int n in
  let rec f acc i l =
    if i = n then BatList.rev acc,l else
      match l with
      | h::tl -> f (h::acc) (i+1) tl
      | _     -> failwith "firstN"
  in
  f [] 0 l

let nth_tail n l =
  let rec aux n l =
    if n=0 then l else aux (n - 1) (BatList.tl l)
  in
  aux (Z.to_int n) l

let prefix l =
  match BatList.rev l with
  | hd::tl -> BatList.rev tl, hd
  | _ -> failwith "impossible"

let mk_ref a = ref a

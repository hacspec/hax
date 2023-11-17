open Base

let ( << ) f g x = f (g x)
let ( >> ) f g x = g (f x)
let ( &&& ) (f : 'a -> 'b) (g : 'a -> 'c) (x : 'a) : 'b * 'c = (f x, g x)

let ( *** ) (f : 'a -> 'b) (g : 'c -> 'd) ((l, r) : 'a * 'c) : 'b * 'd =
  (f l, g r)

let map_fst f = f *** Fn.id
let map_snd g = Fn.id *** g
let map_fst3 f (x, y, z) = (f x, y, z)
let map_snd3 f (x, y, z) = (x, f y, z)
let map_thd3 f (x, y, z) = (x, y, f z)
let fst3 (x, _, _) = x
let snd3 (_, y, _) = y
let thd3 (_, _, z) = z
let curry f x y = f (x, y)
let uncurry f (x, y) = f x y
let curry3 f x y z = f (x, y, z)
let uncurry3 f (x, y, z) = f x y z
let tup2 a b = (a, b)
let ( let* ) x f = Option.bind ~f x
let some_if_true = function true -> Some () | _ -> None

let map_first_letter (f : string -> string) (s : string) =
  let first, rest = String.(prefix s 1, drop_prefix s 1) in
  f first ^ rest

let rec split_list_once ~equal ~needle ~acc subject =
  match subject with
  | [] -> (List.rev acc, [])
  | hd :: tl ->
      if List.is_prefix subject ~prefix:needle ~equal then
        (List.rev acc, List.drop subject (List.length needle))
      else split_list_once ~equal ~needle ~acc:(hd :: acc) tl

let split_list ~equal ~needle (subject : 'a list) : 'a list list =
  let rec h l =
    match split_list_once ~equal ~needle ~acc:[] l with
    | l, [] -> [ l ]
    | l, r -> l :: h r
  in
  h subject

let first_letter s = String.prefix s 1
let is_uppercase s = String.equal s (String.uppercase s)
let is_lowercase s = String.equal s (String.lowercase s)
let start_uppercase = first_letter >> is_uppercase
let start_lowercase = first_letter >> is_lowercase
let string_to_int s = try Some (Int.of_string s) with _ -> None

let split_str (s : string) ~(on : string) : string list =
  split_list ~equal:Char.equal ~needle:(String.to_list on) (String.to_list s)
  |> List.map ~f:String.of_char_list

let last_init (l : 'a list) : ('a list * 'a) option =
  Option.both (List.drop_last l) (List.last l)

let inits (type a) (l : a list) : (a list * a) list =
  List.fold_map ~init:[]
    ~f:(fun trace x ->
      let trace = trace @ [ x ] in
      (trace, (trace, x)))
    l
  |> snd

let tabsize = 2
let newline_indent depth : string = "\n" ^ String.make (tabsize * depth) ' '

module Command = struct
  type output = { stderr : string; stdout : string }

  let run (command : string) (stdin_string : string) : output =
    let stdout, stdin, stderr =
      Unix.open_process_full command (Unix.environment ())
    in
    Unix.set_close_on_exec @@ Unix.descr_of_in_channel stdout;
    Unix.set_close_on_exec @@ Unix.descr_of_in_channel stderr;
    Out_channel.(
      output_string stdin stdin_string;
      flush stdin;
      close stdin);
    let strout = In_channel.input_all stdout in
    let strerr = In_channel.input_all stderr |> Stdlib.String.trim in
    Unix.close @@ Unix.descr_of_in_channel stdout;
    Unix.close @@ Unix.descr_of_in_channel stderr;
    { stdout = strout; stderr = strerr }
end

module MyInt64 = struct
  include Base.Int64

  let t_of_yojson (json : Yojson.Safe.t) : t =
    match json with
    | `Intlit s -> of_string s
    | `Int i -> of_int i
    | _ -> failwith "Couldn't parse MyInt64.t"

  let yojson_of_t (int64 : t) : Yojson.Safe.t = `Intlit (to_string int64)
end

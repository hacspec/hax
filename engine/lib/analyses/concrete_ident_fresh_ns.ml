open! Prelude
module DefId = Concrete_ident_defid
open Concrete_ident_view

module T = struct
  type t = { id : int; path_hints : DefId.t list; name_hints : string list }
  [@@deriving show, yojson, hash, compare, sexp, hash, eq]
end

include T

let make =
  let state = ref 0 in
  fun (path_hints : DefId.t list) (name_hints : string list) ->
    state := !state + 1;
    { id = !state; path_hints; name_hints }

module Path = struct
  module T = struct
    type t = disambiguated_string list [@@deriving eq, compare, sexp, hash]
  end

  include T
  include Comparator.Make (T)
end

(** A map from fresh namespace ids to view paths *)
let per_ns :
    ( int,
      (Path.t, _) Prelude.Set.t * disambiguated_string list option )
    Hashtbl.t =
  Hashtbl.create (module Int)

let register (ns : t) (did : DefId.t) =
  let default : (_, Path.comparator_witness) Set.t * _ option =
    (Set.empty (module Path), None)
  in
  Hashtbl.update per_ns ns.id
    ~f:
      ( Option.value ~default >> fun (set, opt) ->
        let path = (of_def_id did).path in
        (Set.add set path, opt) )

let get_path (ns : t) : disambiguated_string list =
  let f paths =
    let prefix =
      Set.to_list paths
      |> List.longest_prefix ~eq:[%equal: disambiguated_string]
    in
    let chunks =
      Sequence.append
        (Sequence.of_list
           (prefix
           @ List.concat_map
               ~f:(fun did ->
                 (of_def_id did).path |> List.last |> Option.to_list)
               ns.path_hints
           @ List.map
               ~f:(fun data ->
                 Concrete_ident_view.{ disambiguator = Int64.zero; data })
               ns.name_hints))
        (Sequence.unfold ~init:0 ~f:(fun id ->
             Some
               ( Concrete_ident_view.
                   {
                     disambiguator = Int64.of_int id;
                     data = "hax_" ^ Int.to_string ns.id ^ "_fresh_ns";
                   },
                 id + 1 )))
    in
    let all_paths =
      DefId.list_all () |> List.map ~f:(fun x -> (of_def_id x).path) |> ref
    in
    Sequence.take_while
      (Sequence.mapi ~f:(fun i n -> (Int.equal i 0, n)) chunks)
      ~f:(fun (is_first, chunk) ->
        let remaining =
          List.filter_map
            ~f:(function
              | hd :: tl when [%equal: disambiguated_string] hd chunk -> Some tl
              | _ -> None)
            !all_paths
        in
        all_paths := remaining;
        (not (List.is_empty remaining)) || is_first)
    |> Sequence.map ~f:snd |> Sequence.to_list
  in
  Hashtbl.update_and_return per_ns ns.id
    ~f:
      ( Option.value ~default:(Set.empty (module Path), None)
      >> fun (paths, alloc) ->
        ( paths,
          alloc
          |> Option.value_or_thunk ~default:(fun () -> f paths)
          |> Option.some ) )
  |> snd |> Option.value_exn

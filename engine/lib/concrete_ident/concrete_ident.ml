open Base
open Utils

module Non_empty_list = struct
  include Non_empty_list

  let t_of_yojson : (Yojson.Safe.t -> 'a) -> Yojson.Safe.t -> 'a t =
   fun f x -> list_of_yojson f x |> Non_empty_list.of_list_exn

  let yojson_of_t : ('a -> Yojson.Safe.t) -> 'a t -> Yojson.Safe.t =
   fun f x -> Non_empty_list.to_list x |> yojson_of_list f

  let t_of_sexp f s = List.t_of_sexp f s |> Non_empty_list.of_list_exn
  let sexp_of_t f x = Non_empty_list.to_list x |> List.sexp_of_t f
end

type t = { crate : string; path : string Non_empty_list.t }
[@@deriving show, yojson, compare, sexp, eq]

let show (s : t) : string =
  s.crate ^ "::" ^ String.concat ~sep:"::" @@ Non_empty_list.to_list s.path

let pp (fmt : Caml.Format.formatter) (s : t) : unit =
  Caml.Format.pp_print_string fmt @@ show s

let crate { crate; _ } = crate
let path { path; _ } = path

type name = Concrete_ident_generated.name

let string_of_def_path_item : Types.def_path_item -> string option = function
  | TypeNs s | ValueNs s | MacroNs s | LifetimeNs s -> Some s
  | _ -> None

let string_of_disambiguated_def_path_item
    (x : Types.disambiguated_def_path_item) : string option =
  string_of_def_path_item x.data

let of_def_id (def_id : Types.def_id) : t =
  {
    crate = def_id.krate;
    path =
      def_id.path
      |> List.filter_map ~f:string_of_disambiguated_def_path_item
      |> Non_empty_list.of_list_exn;
  }

let mk : name -> t = Concrete_ident_generated.def_id_of >> of_def_id
let eq_name : name -> t -> bool = fun n -> [%equal: t] @@ mk n

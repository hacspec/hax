open Prelude
open Types

type t = Location.t Dual.t * Location.t option Dual.t * meta
[@@deriving show, eq]

let to_points (pts : t list) : point list =
  List.map pts ~f:Option.some
  |> Fn.flip List.append [ None ]
  |> List.folding_map ~init:None ~f:(fun acc x ->
         let prev_end =
           match (acc, x) with
           | Some end_, Some (start, _, _)
             when [%eq: Location.t] start.Dual.gen end_.Dual.gen |> not ->
               Some end_
           | Some end_, None -> Some end_
           | _ -> None
         in
         let out, end_ =
           match x with
           | Some (start, end_, meta) ->
               ([ (start, Some meta) ], Dual.transpose ~default:start end_)
           | None -> ([], None)
         in
         ( end_,
           (prev_end |> Option.map ~f:(fun e -> (e, None)) |> Option.to_list)
           @ out ))
  |> List.concat

let from_points : point list -> t list =
  List.rev
  >> List.folding_map
       ~init:(None, Map.empty (module Int))
       ~f:(fun (gen_loc_0, src_locs) ((loc_start : _ Dual.t), meta) ->
         match meta with
         | Some meta ->
             let src_loc_0 = Map.find src_locs meta.file_offset in
             let src_locs =
               Map.set src_locs ~key:meta.file_offset ~data:loc_start.src
             in
             let loc_end = Dual.{ gen = gen_loc_0; src = src_loc_0 } in
             ((Some loc_start.gen, src_locs), Some (loc_start, loc_end, meta))
         | None -> ((Some loc_start.gen, src_locs), None))
  >> List.filter_map ~f:Fn.id >> List.rev

open Base
open Ppx_yojson_conv_lib.Yojson_conv.Primitives
open Utils
open Ast

module Make (F : Features.T) = struct
  module AST = Ast.Make (F)
  module U = Ast_utils.Make (F)
  open Ast
  open AST

  let ident_of (item : item) : Concrete_ident.t = item.ident

  module Namespace = struct
    module T = struct
      type t = string list [@@deriving show, yojson, compare, sexp, eq, hash]
    end

    module TT = struct
      include T
      include Comparator.Make (T)
    end

    include TT
    module Set = Set.M (TT)

    let of_concrete_ident ci : t =
      let krate, path = Concrete_ident.DefaultViewAPI.to_namespace ci in
      krate :: path
  end

  module ItemGraph = struct
    module G = Graph.Persistent.Digraph.Concrete (Concrete_ident)

    let vertices_of_item (i : item) : G.V.t list =
      let ( @ ) = Set.union in
      let v = U.Reducers.collect_concrete_idents in
      let concat_map f =
        List.map ~f >> Set.union_list (module Concrete_ident)
      in
      let set =
        match i.v with
        | Fn { name = _; generics; body; params } ->
            v#visit_generics () generics
            @ v#visit_expr () body
            @ concat_map (v#visit_param ()) params
        | TyAlias { name = _; generics; ty } ->
            v#visit_generics () generics @ v#visit_ty () ty
        | Type { name = _; generics; variants; is_struct = (_ : bool) } ->
            v#visit_generics () generics
            @ concat_map (v#visit_variant ()) variants
        | IMacroInvokation { macro; argument = (_ : string); span; witness = _ }
          ->
            v#visit_concrete_ident () macro @ v#visit_span () span
        | Trait { name = _; generics; items } ->
            v#visit_generics () generics
            @ concat_map (v#visit_trait_item ()) items
        | Impl { generics; self_ty; of_trait; items } ->
            v#visit_generics () generics
            @ v#visit_ty () self_ty
            @ v#visit_global_ident () (fst of_trait)
            @ concat_map (v#visit_generic_value ()) (snd of_trait)
            @ concat_map (v#visit_impl_item ()) items
        | Use _ | HaxError _ | NotImplementedYet ->
            Set.empty (module Concrete_ident)
      in
      set |> Set.to_list

    let vertices_of_items : item list -> G.E.t list =
      List.concat_map ~f:(fun i ->
          vertices_of_item i |> List.map ~f:(Fn.const i.ident &&& Fn.id))

    let of_items : item list -> G.t =
      vertices_of_items >> List.fold ~init:G.empty ~f:(G.add_edge >> uncurry)

    module MutRec = struct
      module Bundle = struct
        type t = concrete_ident list

        let namespaces_of : t -> Namespace.Set.t =
          List.map ~f:Namespace.of_concrete_ident
          >> Set.of_list (module Namespace)

        let homogeneous_namespace (ns : t) : bool =
          Set.length (namespaces_of ns) <= 1
      end

      type t = {
        mut_rec_bundles : Bundle.t list;
        non_mut_rec : concrete_ident list;
      }

      module SCC = Graph.Components.Make (G)

      let of_graph (g : G.t) : t =
        let is_mut_rec_with_itself x = G.mem_edge g x x in
        let mut_rec_bundles, non_mut_rec =
          SCC.scc_list g
          |> List.partition_map ~f:(function
               | [] -> failwith "scc_list returned empty cluster"
               | [ x ] when is_mut_rec_with_itself x |> not -> Second x
               | bundle -> First bundle)
        in
        { mut_rec_bundles; non_mut_rec }
    end
  end

  module ModGraph = struct
    module G = Graph.Persistent.Digraph.Concrete (Namespace)
  end

  (* Construct the new item `f item` (say `item'`), and create a
     "symbolic link" to `item'`. Returns a pair that consists in the
     symbolic link and in `item'`. *)
  let shallow_copy (f : item -> item) (item : item) : item * item =
    let item' = f item in
    ( {
        item with
        v =
          (match item.v with
          | Fn { name; generics; body; params } ->
              let e = GlobalVar (`Concrete item'.ident) in
              Fn { name; generics; body = { body with e }; params }
          | _ -> failwith "unimplemented");
      },
      item' )

  let name_me (items : item list) : item list =
    let g = ItemGraph.of_items items in
    let from_ident ident : item =
      List.find_exn ~f:(fun i -> [%equal: Concrete_ident.t] i.ident ident) items
    in
    let non_mut_rec, mut_rec_bundles =
      let b = ItemGraph.MutRec.of_graph g in
      let f = List.map ~f:from_ident in
      (f b.non_mut_rec, List.map ~f b.mut_rec_bundles)
    in
    let transform (bundle : item list) =
      prerr_endline @@ "###### TRANSFORM";
      prerr_endline @@ "transform bundle=" ^ [%show: item list] bundle;
      let ns : Concrete_ident.t =
        Concrete_ident.Create.fresh_module ~from:(List.map ~f:ident_of bundle)
      in
      let new_name_under_ns : Concrete_ident.t -> Concrete_ident.t =
        Concrete_ident.Create.move_under ~new_parent:ns
      in
      let renamings =
        List.map ~f:(ident_of >> (Fn.id &&& new_name_under_ns)) bundle
        |> Map.of_alist_exn (module Concrete_ident)
      in
      let rename =
        let renamer _lvl i = Map.find renamings i |> Option.value ~default:i in
        (U.Mappers.rename_concrete_idents renamer)#visit_item ExprLevel
      in
      let shallow, bundle =
        List.map ~f:(shallow_copy rename) bundle |> List.unzip
      in
      prerr_endline @@ "shallow=" ^ [%show: item list] shallow;
      prerr_endline @@ "bundle=" ^ [%show: item list] bundle;
      prerr_endline @@ "###### END";
      bundle @ shallow
    in
    let mut_rec_bundles =
      List.map
        ~f:(fun bundle ->
          if
            List.map ~f:ident_of bundle
            |> ItemGraph.MutRec.Bundle.homogeneous_namespace
          then bundle
          else transform bundle)
        mut_rec_bundles
    in
    non_mut_rec @ List.concat_map ~f:Fn.id mut_rec_bundles
end

open! Prelude

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
    module Topological = Graph.Topological.Make_stable (G)
    module Oper = Graph.Oper.P (G)

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
        | Impl { generics; self_ty; of_trait; items; parent_bounds } ->
            v#visit_generics () generics
            @ v#visit_ty () self_ty
            @ v#visit_global_ident () (fst of_trait)
            @ concat_map (v#visit_generic_value ()) (snd of_trait)
            @ concat_map (v#visit_impl_item ()) items
            @ concat_map
                (fun (ie, ii) ->
                  v#visit_impl_expr () ie @ v#visit_impl_ident () ii)
                parent_bounds
        | Alias { name = _; item } -> v#visit_concrete_ident () item
        | Use _ | Quote _ | HaxError _ | NotImplementedYet ->
            Set.empty (module Concrete_ident)
      in
      set |> Set.to_list

    let vertices_of_items : item list -> G.E.t list =
      List.concat_map ~f:(fun i ->
          vertices_of_item i |> List.map ~f:(Fn.const i.ident &&& Fn.id))

    let of_items (items : item list) : G.t =
      let init =
        List.fold ~init:G.empty ~f:(fun g -> ident_of >> G.add_vertex g) items
      in
      vertices_of_items items |> List.fold ~init ~f:(G.add_edge >> uncurry)

    let transitive_dependencies_of (g : G.t) (selection : Concrete_ident.t list)
        : Concrete_ident.t Hash_set.t =
      let set = Hash_set.create (module Concrete_ident) in
      let rec visit vertex =
        if Hash_set.mem set vertex |> not then (
          Hash_set.add set vertex;
          G.iter_succ visit g vertex)
      in
      List.filter ~f:(G.mem_vertex g) selection |> List.iter ~f:visit;
      set

    let transitive_dependencies_of_items (items : item list)
        ?(graph = of_items items) (selection : Concrete_ident.t list) :
        item list =
      let set = transitive_dependencies_of graph selection in
      items |> List.filter ~f:(ident_of >> Hash_set.mem set)

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

      let all_homogeneous_namespace (g : G.t) =
        List.for_all ~f:Bundle.homogeneous_namespace
          (of_graph g).mut_rec_bundles
    end

    open Graph.Graphviz.Dot (struct
      include G

      let graph_attributes _ = []
      let default_vertex_attributes _ = []
      let vertex_name i = "\"" ^ Concrete_ident.show i ^ "\""

      let vertex_attributes i =
        [ `Label (Concrete_ident.DefaultViewAPI.to_definition_name i) ]

      let get_subgraph i =
        let ns = Namespace.of_concrete_ident i in
        let sg_name = String.concat ~sep:"__" ns in
        let label = String.concat ~sep:"::" ns in
        let open Graph.Graphviz.DotAttributes in
        Some { sg_name; sg_attributes = [ `Label label ]; sg_parent = None }

      let default_edge_attributes _ = []
      let edge_attributes _ = []
    end)

    let print oc items = output_graph oc (of_items items)
  end

  module ModGraph = struct
    module G = Graph.Persistent.Digraph.Concrete (Namespace)

    let of_items (items : item list) : G.t =
      let ig = ItemGraph.of_items items in
      assert (ItemGraph.MutRec.all_homogeneous_namespace ig);
      List.map ~f:(ident_of >> (Namespace.of_concrete_ident &&& Fn.id)) items
      |> Map.of_alist_multi (module Namespace)
      |> Map.map
           ~f:
             (List.concat_map
                ~f:
                  (ItemGraph.G.succ ig
                  >> List.map ~f:Namespace.of_concrete_ident)
             >> Set.of_list (module Namespace)
             >> Set.to_list)
      |> Map.to_alist
      |> List.concat_map ~f:(fun (x, ys) -> List.map ~f:(fun y -> (x, y)) ys)
      |> List.fold ~init:G.empty ~f:(G.add_edge >> uncurry)

    module SCC = Graph.Components.Make (G)

    open Graph.Graphviz.Dot (struct
      include G

      let graph_attributes _ = []
      let default_vertex_attributes _ = []
      let vertex_name ns = "\"" ^ String.concat ~sep:"::" ns ^ "\""
      let vertex_attributes _ = []
      let get_subgraph _ = None
      let default_edge_attributes _ = []
      let edge_attributes _ = []
    end)

    let print oc items =
      let g = of_items items in
      let complicated_ones =
        SCC.scc_list g
        |> List.concat_map ~f:(function [] | [ _ ] -> [] | bundle -> bundle)
      in
      let g =
        List.concat_map
          ~f:(fun ns ->
            List.map
              ~f:(fun y -> (ns, y))
              (G.succ g ns
              |> List.filter
                   ~f:(List.mem ~equal:[%equal: Namespace.t] complicated_ones)))
          complicated_ones
        |> List.fold ~init:G.empty ~f:(G.add_edge >> uncurry)
      in
      output_graph oc g
  end

  let ident_list_to_string =
    List.map ~f:Concrete_ident.DefaultViewAPI.show >> String.concat ~sep:", "

  let sort (items : item list) : item list =
    let g = ItemGraph.of_items items |> ItemGraph.Oper.mirror in
    let lookup (name : concrete_ident) =
      List.find ~f:(ident_of >> Concrete_ident.equal name) items
    in
    let items' =
      ItemGraph.Topological.fold List.cons g []
      |> List.filter_map ~f:lookup |> List.rev
    in
    assert (
      let of_list =
        List.map ~f:ident_of >> Set.of_list (module Concrete_ident)
      in
      let items = of_list items in
      let items' = of_list items' in
      Set.equal items items');
    items'

  let filter_by_inclusion_clauses' (clauses : Types.inclusion_clause list)
      (items : item list) : item list * Concrete_ident.t Hash_set.t =
    let graph = ItemGraph.of_items items in
    let of_list = Set.of_list (module Concrete_ident) in
    let selection = List.map ~f:ident_of items |> of_list in
    let deps_of =
      let to_set = Hash_set.to_list >> of_list in
      Set.to_list >> ItemGraph.transitive_dependencies_of graph >> to_set
    in
    let show_ident_set =
      Set.to_list
      >> List.map ~f:Concrete_ident.DefaultViewAPI.show
      >> List.map ~f:(fun s -> " - " ^ s)
      >> String.concat ~sep:"\n"
    in
    let show_inclusion_clause Types.{ kind; namespace } =
      (match kind with
      | Excluded -> "-"
      | SignatureOnly -> "+:"
      | Included deps_kind -> (
          match deps_kind with
          | Transitive -> "+"
          | Shallow -> "+~"
          | None' -> "+!"))
      ^ "["
      ^ (List.map
           ~f:(function Glob One -> "*" | Glob Many -> "**" | Exact s -> s)
           namespace.chunks
        |> String.concat ~sep:"::")
      ^ "]"
    in
    let items_drop_body = Hash_set.create (module Concrete_ident) in
    let apply_clause selection' (clause : Types.inclusion_clause) =
      let matches = Concrete_ident.matches_namespace clause.Types.namespace in
      let matched0 = Set.filter ~f:matches selection in
      let with_deps, drop_bodies =
        match clause.kind with
        | Included Transitive -> (true, false)
        | Included Shallow -> (true, true)
        | Included None' -> (false, false)
        | SignatureOnly -> (false, true)
        | Excluded -> (false, false)
      in
      let matched = matched0 |> if with_deps then deps_of else Fn.id in
      if drop_bodies then (
        Set.iter ~f:(Hash_set.add items_drop_body) matched;
        Set.iter ~f:(Hash_set.remove items_drop_body) matched0);
      Logs.info (fun m ->
          m "The clause [%s] will %s the following Rust items:\n%s"
            (show_inclusion_clause clause)
            (match clause.kind with Excluded -> "remove" | _ -> "add")
          @@ show_ident_set matched);
      let set_op =
        match clause.kind with
        | Included _ | SignatureOnly -> Set.union
        | Excluded -> Set.diff
      in
      let result = set_op selection' matched in
      result
    in
    let selection = List.fold ~init:selection ~f:apply_clause clauses in
    Logs.info (fun m ->
        m "The following Rust items are going to be extracted:\n%s"
        @@ show_ident_set selection);
    (List.filter ~f:(ident_of >> Set.mem selection) items, items_drop_body)

  let filter_by_inclusion_clauses ~drop_impl_bodies
      (clauses : Types.inclusion_clause list) (items : item list) : item list =
    let f = filter_by_inclusion_clauses' clauses in
    let selection =
      let items', items_drop_body = f items in
      let items', _ =
        (* when one includes only shallow dependencies, we just remove bodies *)
        List.map
          ~f:(fun item ->
            if Hash_set.mem items_drop_body (ident_of item) then
              (U.Mappers.drop_bodies drop_impl_bodies)#visit_item () item
            else item)
          items'
        |> f
      in
      List.map ~f:ident_of items' |> Set.of_list (module Concrete_ident)
    in
    List.filter ~f:(ident_of >> Set.mem selection) items

  (* Construct the new item `f item` (say `item'`), and create a
     "symbolic link" to `item'`. Returns a pair that consists in the
     symbolic link and in `item'`. *)
  let shallow_copy (f : item -> item) (item : item) : item * item =
    let item' = f item in
    ({ item with v = Alias { name = item.ident; item = item'.ident } }, item')

  let name_me' (items : item list) : item list =
    let g = ItemGraph.of_items items in
    let from_ident ident : item option =
      List.find ~f:(fun i -> [%equal: Concrete_ident.t] i.ident ident) items
    in
    let non_mut_rec, mut_rec_bundles =
      let b = ItemGraph.MutRec.of_graph g in
      let f = List.filter_map ~f:from_ident in
      (f b.non_mut_rec, List.map ~f b.mut_rec_bundles)
    in
    let transform (bundle : item list) =
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

  let name_me (items : item list) : item list =
    let h f name items =
      let file = Stdlib.open_out @@ "/tmp/graph_" ^ name ^ ".dot" in
      f file items;
      Stdlib.close_out file
    in
    h ItemGraph.print "items_before" items;
    let items = name_me' items in
    h ItemGraph.print "items_after" items;
    h ModGraph.print "mods" items;
    items
end

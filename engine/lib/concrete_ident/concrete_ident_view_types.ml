open! Prelude

(** This modules defines what is the view over a concrete identifiers.

    Hax manipulates concrete identifiers (that is global identifiers refering to
    concrete Rust items -- not built-in operators) as raw Rust identifiers
    augmented with some metadata.

    Rust represents identifiers as a crate and a path. Each chunk of the path is
    roughly a level of nest in Rust. The path lacks informations about
    definition kinds.

    There is two kinds of nesting for items.
    - Confort: e.g. the user decides to embed a struct within a function to work
      with it locally.
    - Relational: e.g. an associated method has to be under a trait, or a field
      as to be under a constructor.

    This module provides a view to those paths: a path in the view is a list of
    smaller relational paths. For instance, consider the following piece of
    code:

    {@rust[
      mod a {
          impl MyTrait for MyType {
              fn assoc_fn() {
                  struct LocalStruct {
                      field: u8,
                  };
              }
          }
      }
    ]}

    Here, the Rust raw definition identifier of [LocalStruct] is roughly
    [a::my_crate::<Impl 0>::assoc_fn::LocalStruct::field].

    The view for [LocalStruct] looks like:
    [{
      {
        path: ["mycrate"; "a"],
        name_path: [
          `AssociatedItem ("assoc_fn", `Impl 0);
          `Field ("field", `Constructor ("LocalStruct", `Struct "LocalStruct"))
        ]
      }
    }]
*)

type disambiguator = Int64.t
[@@deriving show, hash, compare, sexp, hash, eq, map]
(** A [Int64.t] disambiguator: this is given by Rust. *)

(** A string with a disambiguator. *)
module DisambiguatedString = struct
  module T = struct
    type t = { disambiguator : disambiguator; data : string }
    [@@deriving show, hash, compare, sexp, hash, eq, map]
  end

  include T
  include Base.Comparator.Make (T)

  let pure data = { disambiguator = Int64.zero; data }
end

(** A "module and crate"-only path. This is the longest `mod` suffix of a
  definition identifier path. This is a list of disambiguated strings. *)
module ModPath = struct
  module T = struct
    open struct
      module T = struct
        type t = DisambiguatedString.t list
        [@@deriving show, hash, compare, sexp, hash, eq]
      end
    end

    include T
    include Base.Comparator.Make (T)
  end

  include T
  module Map = Map.M (T)
end

(** A relational path is a path composed of relational chunks. *)
module RelPath = struct
  (** A relational chunk is a short path describing "mandatory" nestings between
      items: e.g. a field below a struct, an enum below an enum variants, etc. 

    The types defined by this module are indexed by two other types: ['name] and
    ['disambiguator]. This helps for instrumenting the view to perform
    additional operations: see [collect_either], [collect] and [root].
    *)
  module Chunk = struct
    type 'name type_definition =
      [ `Enum of 'name | `Struct of 'name | `Union of 'name ]
    (** A type can be an enum, a struct or a union. A type is standalone: it has no mandatory parent item. *)

    and 'name constructor = [ `Constructor of 'name * 'name type_definition ]
    (** A constructor always has a parent type definition. *)

    and 'name maybe_associated = [ `Fn of 'name | `Const of 'name ]
    [@@deriving show, hash, compare, sexp, hash, eq, map]
    (** Helper type for function and constants: those exists both as associated
      in an impl block or a trait, and as standalone. *)

    type 'name associated = [ 'name maybe_associated | `Type of 'name ]
    (** An associated item. This is pulled out of [`AssociatedItem] below:
      otherwise, some PPX is broken...  *)

    and ('name, 'disambiguator) assoc_parent =
      [ `Impl of
        'disambiguator * [ `Inherent | `Trait ] * Types.impl_infos option
      | `Trait of 'name * [ `Alias ] option ]
    [@@deriving show, hash, compare, sexp, hash, eq, map]
    (** The parent of an associated item can be an impl or a trait. *)

    type ('name, 'disambiguator) poly =
      [ 'name type_definition
      | 'name constructor
      | 'name maybe_associated
      | ('name, 'disambiguator) assoc_parent
      | `Use of 'disambiguator
      | `AnonConst of 'disambiguator
      | `TraitAlias of 'name
      | `Foreign of 'disambiguator
      | `ForeignTy of 'name
      | `TyAlias of 'name
      | `ExternCrate of 'name
      | `Opaque of 'disambiguator
        (** This is e.g.: {[
          fn f() -> impl Clone {}
          fn g() {
            f();
          }
        ]} 
        Here, the type of `f()` is `<f::OpaqueTy>`.
        *)
      | `Static of 'name
      | `Macro of 'name
      | `AssociatedItem of
        'name associated * ('name, 'disambiguator) assoc_parent
      | `Mod of 'name
      | `GlobalAsm of 'disambiguator
      | `Field of 'name * 'name constructor ]
    [@@deriving show, hash, compare, sexp, hash, eq, map]
    (** [poly] is the (polymorphic) type for a relational chunk: it defines what is a chunk. *)

    type t = (DisambiguatedString.t, disambiguator) poly
    [@@deriving show, hash, compare, sexp, hash, eq]
    (** [t] is the natural instantiation of [poly]. *)

    (** Transforms a [t] into a [poly] with annotated strings instead of just
        disambiguators. This adds names to the disambiguator-only constructs defined in
        [poly]. *)
    let add_strings ?(impl = "impl") ?(anon_const = "anon_const")
        ?(foreign = "foregin") ?(global_asm = "global_asm") (n : t) :
        (DisambiguatedString.t, DisambiguatedString.t) poly =
      let f disambiguator =
        DisambiguatedString.{ disambiguator; data = impl }
      in
      match map_poly Fn.id f n with
      | `AnonConst o -> `AnonConst { o with data = anon_const }
      | `Foreign o -> `Foreign { o with data = foreign }
      | `GlobalAsm o -> `GlobalAsm { o with data = global_asm }
      | n -> n

    (** Erases names from a [t]. *)
    let only_disambiguators : t -> (disambiguator, disambiguator) poly =
      map_poly DisambiguatedString.(fun ds -> ds.disambiguator) Fn.id

    (** Collects all the data of a [t], from the child to the parent. *)
    let rec collect_either :
          'n 'd. ('n, 'd) poly -> [ `N of 'n | `D of 'd ] list = function
      | `Opaque n
      | `GlobalAsm n
      | `AnonConst n
      | `Impl (n, _, _)
      | `Use n
      | `Foreign n ->
          [ `D n ]
      | `Static n
      | `Macro n
      | `Enum n
      | `Struct n
      | `Union n
      | `TyAlias n
      | `TraitAlias n
      | `Fn n
      | `Const n
      | `Trait (n, _)
      | `ExternCrate n
      | `Mod n
      | `ForeignTy n ->
          [ `N n ]
      | `AssociatedItem ((`Fn a | `Const a | `Type a), b) ->
          `N a :: collect_either (b :> _ poly)
      | `Constructor (a, b) -> `N a :: collect_either (b :> _ poly)
      | `Field (a, b) -> `N a :: collect_either (b :> _ poly)

    (** Same as [collect_either], but works on a [poly] whose ['name] and
      ['disambiguator] happen to be the same type. *)
    let collect : 'a. ('a, 'a) poly -> 'a list =
     fun n -> collect_either n |> List.map ~f:(function `D v | `N v -> v)

    (** Find the root of a [poly]. *)
    let root : 'a. ('a, 'a) poly -> 'a = fun x -> collect x |> List.last_exn
  end

  type t = Chunk.t list [@@deriving show, hash, compare, sexp, hash, eq]
end

type t = { mod_path : ModPath.t; rel_path : RelPath.t }
[@@deriving show, hash, compare, sexp, hash, eq]
(** Invariant: [name_path] is non-empty *)

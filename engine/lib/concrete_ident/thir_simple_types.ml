open! Prelude
module View = Concrete_ident_view

(** Interprets a type as a "simple type". 
    A simple type is a type for which, in a given scope, we can give a non-ambiguous string identifier.
  
    This is useful for naming local impls.

    Examples of "simple" types:
     - primitive types (e.g. u8, u16)
     - enums/structs/unions defined in [namespace], when:
       + all their generic arguments are instantiated to a simple type
     - a reference to a simple type
     - a slice to a simple type
     - a tuple of simple types of arity zero (e.g. no ADTs of non-zero arity)
*)
let to_string ~(namespace : View.ModPath.t) :
    Types.node_for__ty_kind -> string option =
  let escape =
    let re = Re.Pcre.regexp "_((?:e_)*)of_" in
    let f group = "_e_" ^ Re.Group.get group 1 ^ "of_" in
    Re.replace ~all:true re ~f
  in
  let adt def_id =
    let* def_id = Explicit_def_id.of_def_id ~constructor:false def_id in
    let view = View.of_def_id def_id in
    let* () =
      [%equal: View.ModPath.t] view.mod_path namespace |> some_if_true
    in
    let* last = expect_singleton view.rel_path in
    let* name =
      match last with
      | (`Struct d | `Union d | `Enum d)
        when Int64.(equal (of_int 0) d.disambiguator) ->
          Some d.data
      | _ -> None
    in
    escape name |> Option.some
  in
  let arity0 (ty : Types.node_for__ty_kind) =
    match ty.Types.value with
    | Bool -> Some "bool"
    | Char -> Some "char"
    | Str -> Some "str"
    | Never -> Some "never"
    | Int Isize -> Some "isize"
    | Int I8 -> Some "i8"
    | Int I16 -> Some "i16"
    | Int I32 -> Some "i32"
    | Int I64 -> Some "i64"
    | Int I128 -> Some "i128"
    | Uint Usize -> Some "usize"
    | Uint U8 -> Some "u8"
    | Uint U16 -> Some "u16"
    | Uint U32 -> Some "u32"
    | Uint U64 -> Some "u64"
    | Uint U128 -> Some "u128"
    | Float F32 -> Some "f32"
    | Float F64 -> Some "f64"
    | Tuple [] -> Some "unit"
    | Adt { def_id; generic_args = []; _ } -> Option.map ~f:escape (adt def_id)
    | _ -> None
  in
  let apply left right = left ^ "_of_" ^ right in
  let rec arity1 (ty : Types.node_for__ty_kind) =
    match ty.value with
    | Slice sub -> arity1 sub |> Option.map ~f:(apply "slice")
    | Ref (_, sub, _) -> arity1 sub |> Option.map ~f:(apply "ref")
    | Adt { def_id; generic_args = [ Type arg ]; _ } ->
        let* adt = adt def_id in
        let* arg = arity1 arg in
        Some (apply adt arg)
    | Tuple l ->
        let* l = List.map ~f:arity0 l |> Option.all in
        Some ("tuple_" ^ String.concat ~sep:"_" l)
    | _ -> arity0 ty
  in
  arity1

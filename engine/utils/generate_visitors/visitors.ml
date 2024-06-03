open Base
open Types
open Utils

class virtual ['self] reduce =
  object (self : 'self)
    method virtual plus : 'acc -> 'acc -> 'acc
    method virtual zero : 'acc
    method visit_string (_env : 'env) (_s : string) = self#zero

    method visit_prim___tuple_2
        : 't0 't1.
          ('env -> 't0 -> 'acc) ->
          ('env -> 't1 -> 'acc) ->
          'env ->
          't0 * 't1 ->
          'acc =
      fun visit_'t0 visit_'t1 env___var v___payload ->
        match v___payload with
        | x0, x1 ->
            let a0 = visit_'t0 env___var x0 in
            let a1 = visit_'t1 env___var x1 in
            self#plus a0 a1

    method visit_prim___tuple_3
        : 't0 't1 't2.
          ('env -> 't0 -> 'acc) ->
          ('env -> 't1 -> 'acc) ->
          ('env -> 't2 -> 'acc) ->
          'env ->
          't0 * 't1 * 't2 ->
          'acc =
      fun visit_'t0 visit_'t1 visit_'t2 env___var v___payload ->
        match v___payload with
        | x0, x1, x2 ->
            let a0 = visit_'t0 env___var x0 in
            let a1 = visit_'t1 env___var x1 in
            let a2 = visit_'t2 env___var x2 in
            self#plus (self#plus a0 a1) a2

    method visit_prim___tuple_4
        : 't0 't1 't2 't3.
          ('env -> 't0 -> 'acc) ->
          ('env -> 't1 -> 'acc) ->
          ('env -> 't2 -> 'acc) ->
          ('env -> 't3 -> 'acc) ->
          'env ->
          't0 * 't1 * 't2 * 't3 ->
          'acc =
      fun visit_'t0 visit_'t1 visit_'t2 visit_'t3 env___var v___payload ->
        match v___payload with
        | x0, x1, x2, x3 ->
            let a0 = visit_'t0 env___var x0 in
            let a1 = visit_'t1 env___var x1 in
            let a2 = visit_'t2 env___var x2 in
            let a3 = visit_'t3 env___var x3 in
            self#plus (self#plus (self#plus a0 a1) a2) a3

    method visit_option : 'a. ('env -> 'a -> 'acc) -> 'env -> 'a option -> 'acc
        =
      fun visit_'a env___var v___payload ->
        match v___payload with
        | Some x0 ->
            let a0 = visit_'a env___var x0 in
            a0
        | None -> self#zero

    method visit_Type__t : 'env -> Type.t -> 'acc =
      fun env___var v___payload ->
        let acc___typ = self#visit_string env___var v___payload.typ in
        let acc___args =
          self#visit_list self#visit_Type__t env___var v___payload.args
        in
        self#plus acc___typ acc___args

    method visit_Record__field : 'env -> Record.field -> 'acc =
      fun env___var v___payload ->
        self#visit_prim___tuple_2 self#visit_string self#visit_Type__t env___var
          v___payload

    method visit_Record__t : 'env -> Record.t -> 'acc =
      fun env___var v___payload ->
        self#visit_list self#visit_Record__field env___var v___payload

    method visit_VariantPayload__t : 'env -> VariantPayload.t -> 'acc =
      fun env___var v___payload ->
        match v___payload with
        | Record x0 ->
            let a0 = self#visit_Record__t env___var x0 in
            a0
        | Tuple x0 ->
            let a0 = self#visit_list self#visit_Type__t env___var x0 in
            a0
        | None -> self#zero

    method visit_Variant__t : 'env -> Variant.t -> 'acc =
      fun env___var v___payload ->
        let acc___name = self#visit_string env___var v___payload.name in
        let acc___payload =
          self#visit_VariantPayload__t env___var v___payload.payload
        in
        self#plus acc___name acc___payload

    method visit_Result__t
        : 'r 'e.
          ('env -> 'r -> 'acc) ->
          ('env -> 'e -> 'acc) ->
          'env ->
          ('r, 'e) Result.t ->
          'acc =
      fun visit_'r visit_'e env___var v___payload ->
        match v___payload with
        | Ok x0 ->
            let a0 = visit_'r env___var x0 in
            a0
        | Error x0 ->
            let a0 = visit_'e env___var x0 in
            a0

    method visit_Datatype__kind : 'env -> Datatype.kind -> 'acc =
      fun env___var v___payload ->
        match v___payload with
        | Record x0 ->
            let a0 = self#visit_Record__t env___var x0 in
            a0
        | Variant x0 ->
            let a0 = self#visit_list self#visit_Variant__t env___var x0 in
            a0
        | TypeSynonym x0 ->
            let a0 = self#visit_Type__t env___var x0 in
            a0
        | Opaque -> self#zero

    method visit_Datatype__t : 'env -> Datatype.t -> 'acc =
      fun env___var v___payload ->
        let acc___name = self#visit_string env___var v___payload.name in
        let acc___type_vars =
          self#visit_list self#visit_string env___var v___payload.type_vars
        in
        let acc___kind = self#visit_Datatype__kind env___var v___payload.kind in
        self#plus (self#plus acc___name acc___type_vars) acc___kind

    method visit_datatypes : 'env -> Datatype.t list -> 'acc =
      self#visit_list self#visit_Datatype__t

    method visit_list : 'a. ('env -> 'a -> 'acc) -> 'env -> 'a list -> 'acc =
      fun v env this ->
        Base.List.fold ~init:self#zero
          ~f:(fun acc -> v env >> self#plus acc)
          this
  end

let collect_defined_types =
  (object
     inherit [_] reduce as _super
     method plus = Set.union
     method zero = Set.empty (module String)
     method! visit_Datatype__t () dt = Set.singleton (module String) dt.name
  end)
    #visit_datatypes
    ()

let collect_used_types =
  (object (self)
     inherit [_] reduce as super
     method plus = Set.union
     method zero = Set.empty (module String)

     method! visit_Type__t () t =
       let typ = t.typ in
       self#plus
         (if String.is_prefix ~prefix:"'" typ || String.equal typ "list" then
          self#zero
         else Set.singleton (module String) typ)
         (super#visit_Type__t () t)
  end)
    #visit_datatypes
    ()

let collect_undefined_types dts : string list =
  Set.diff (collect_used_types dts) (collect_defined_types dts) |> Set.to_list

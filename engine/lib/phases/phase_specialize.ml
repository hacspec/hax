open! Prelude

module Make (F : Features.T) =
  Phase_utils.MakeMonomorphicPhase
    (F)
    (struct
      let phase_id = [%auto_phase_name auto]

      module A = Ast.Make (F)
      module FB = F
      module B = Ast.Make (F)
      module U = Ast_utils.Make (F)
      module Visitors = Ast_visitors.Make (F)
      open A

      open struct
        open Concrete_ident_generated

        module FnReplace = struct
          type t =
            span:Span.t ->
            typ:ty ->
            f:expr ->
            args:expr list ->
            generic_args:generic_value list ->
            bounds_impls:impl_expr list ->
            trait:(impl_expr * generic_value list) option ->
            expr

          (** Retype a function application: this concretize the types, using concrete types from arguments.  *)
          let retype (fn : t) : t =
           fun ~span ~typ ~f ~args ~generic_args ~bounds_impls ~trait ->
            let f =
              let typ =
                if List.is_empty args then f.typ
                else TArrow (List.map ~f:(fun e -> e.typ) args, typ)
              in
              { f with typ }
            in
            fn ~span ~typ ~f ~args ~generic_args ~bounds_impls ~trait

          (** Gets rid of trait and impl informations. *)
          let remove_traits (fn : t) : t =
           fun ~span ~typ ~f ~args ~generic_args:_ ~bounds_impls:_ ~trait:_ ->
            fn ~span ~typ ~f ~args ~generic_args:[] ~bounds_impls:[] ~trait:None

          (** Monomorphize a function call: this removes any impl references, and concretize types. *)
          let monorphic (fn : t) : t = remove_traits (retype fn)

          let name name : t =
           fun ~span ~typ ~f ~args ~generic_args ~bounds_impls ~trait ->
            let name = Ast.Global_ident.of_name ~value:true name in
            let f = { f with e = GlobalVar name } in
            let e = App { args; f; generic_args; bounds_impls; trait } in
            { typ; span; e }

          let and_then (f1 : t) (f2 : expr -> expr) : t =
           fun ~span ~typ ~f ~args ~generic_args ~bounds_impls ~trait ->
            f1 ~span ~typ ~f ~args ~generic_args ~bounds_impls ~trait |> f2

          let map_args (fn : int -> expr -> expr) : t -> t =
           fun g ~span ~typ ~f ~args ~generic_args ~bounds_impls ~trait ->
            let args = List.mapi ~f:fn args in
            g ~span ~typ ~f ~args ~generic_args ~bounds_impls ~trait
        end

        type pattern = {
          fn : t;
          fn_replace : FnReplace.t;
          args : (expr -> bool) list;
          ret : ty -> bool;
        }
        (** A pattern that helps matching against function applications *)

        type ('a, 'b) predicate = 'a -> 'b option
        (** Instead of working directly with boolean predicate, we
        work with `_ -> _ option` so that we can chain them *)

        (** Constructs a predicate out of predicates and names *)
        let mk' (args : ('a, 'b) predicate list) (ret : ('c, 'd) predicate)
            (fn : t) (fn_replace : FnReplace.t) : pattern =
          let args = List.map ~f:(fun p x -> p x |> Option.is_some) args in
          let ret t = ret t |> Option.is_some in
          { fn; fn_replace; args; ret }

        let mk (args : ('a, 'b) predicate list) (ret : ('c, 'd) predicate)
            (fn : t) (fn_replace : t) : pattern =
          mk' args ret fn (FnReplace.name fn_replace |> FnReplace.monorphic)

        open struct
          let etyp (e : expr) : ty = e.typ
          let tref = function TRef { typ; _ } -> Some typ | _ -> None

          let tapp0 = function
            | TApp { ident; args = [] } -> Some ident
            | _ -> None

          let ( >>& ) (f1 : ('a, 'b) predicate) (f2 : ('b, 'c) predicate) :
              ('a, 'c) predicate =
           fun x -> Option.bind (f1 x) ~f:f2

          let eq : 'a 'b. eq:('a -> 'b -> bool) -> 'a -> ('b, 'b) predicate =
           fun ~eq x x' -> if eq x x' then Some x' else None

          let eq_global_ident :
              t -> (Ast.Global_ident.t, Ast.Global_ident.t) predicate =
            eq ~eq:Ast.Global_ident.eq_name

          let erase : 'a. ('a, unit) predicate = fun _ -> Some ()

          let ( ||. ) (type a b) (f : (a, b) predicate) (g : (a, b) predicate) :
              (a, b) predicate =
           fun x ->
            match (f x, g x) with Some a, _ | _, Some a -> Some a | _ -> None

          let is_int : (ty, unit) predicate =
            tapp0 >>& eq_global_ident Hax_lib__int__Int >>& erase

          let is_prop : (ty, unit) predicate =
            tapp0 >>& eq_global_ident Hax_lib__prop__Prop >>& erase

          let is_bool : (ty, unit) predicate = function
            | TBool -> Some ()
            | _ -> None

          let any _ = Some ()
          let int_any = mk [ etyp >> is_int ] any
          let int_int_any = mk [ etyp >> is_int; etyp >> is_int ] any
          let any_int = mk [ any ] is_int
          let rint_any = mk [ etyp >> (tref >>& is_int) ] any

          let rint_rint_any =
            mk [ etyp >> (tref >>& is_int); etyp >> (tref >>& is_int) ] any

          let any_rint = mk [ any ] (tref >>& is_int)
          let bool_prop = mk [ etyp >> is_bool ] is_prop
          let prop_bool = mk [ etyp >> is_prop ] is_bool

          let arrow : (ty, ty list) predicate = function
            | TArrow (ts, t) -> Some (ts @ [ t ])
            | _ -> None

          let a_to_b a b : _ predicate =
            arrow >> fun x ->
            let* t, u =
              match x with Some [ a; b ] -> Some (a, b) | _ -> None
            in
            let* a = a t in
            let* b = b u in
            Some (a, b)
        end

        let int_replacements =
          [
            int_int_any Core__ops__arith__Add__add
              Rust_primitives__hax__int__add;
            int_int_any Core__ops__arith__Sub__sub
              Rust_primitives__hax__int__sub;
            int_int_any Core__ops__arith__Mul__mul
              Rust_primitives__hax__int__mul;
            int_int_any Core__ops__arith__Div__div
              Rust_primitives__hax__int__div;
            int_int_any Core__ops__arith__Rem__rem
              Rust_primitives__hax__int__rem;
            rint_rint_any Core__cmp__PartialOrd__gt
              Rust_primitives__hax__int__gt;
            rint_rint_any Core__cmp__PartialOrd__ge
              Rust_primitives__hax__int__ge;
            rint_rint_any Core__cmp__PartialOrd__lt
              Rust_primitives__hax__int__lt;
            rint_rint_any Core__cmp__PartialOrd__le
              Rust_primitives__hax__int__le;
            rint_rint_any Core__cmp__PartialEq__ne Rust_primitives__hax__int__ne;
            rint_rint_any Core__cmp__PartialEq__eq Rust_primitives__hax__int__eq;
            any_int Hax_lib__abstraction__Abstraction__lift
              Rust_primitives__hax__int__from_machine;
            any_int Hax_lib__int__ToInt__to_int
              Rust_primitives__hax__int__from_machine;
            int_any Hax_lib__abstraction__Concretization__concretize
              Rust_primitives__hax__int__into_machine;
          ]

        let prop_replacements =
          let name_from_bool = Hax_lib__prop__constructors__from_bool in
          let prop_type =
            let ident =
              Ast.Global_ident.of_name ~value:false Hax_lib__prop__Prop
            in
            TApp { ident; args = [] }
          in
          let bool_prop__from_bool f = bool_prop f name_from_bool in
          let poly n f g =
            let args =
              let prop_or_bool = is_bool ||. is_prop in
              List.init n ~f:(fun _ ->
                  etyp
                  >> (prop_or_bool
                     ||. (a_to_b prop_or_bool prop_or_bool >> erase)))
            in
            let promote_bool (e : A.expr) =
              match e.typ with
              | TBool -> U.call name_from_bool [ e ] e.span prop_type
              | _ -> e
            in
            mk' args is_prop f
              (FnReplace.map_args
                 (fun _ e ->
                   let e = promote_bool e in
                   match e.e with
                   | Closure { params; body; captures } ->
                       let body = promote_bool body in
                       { e with e = Closure { params; body; captures } }
                   | _ -> e)
                 (FnReplace.name g |> FnReplace.monorphic))
          in
          [
            bool_prop__from_bool Hax_lib__abstraction__Abstraction__lift;
            bool_prop__from_bool Hax_lib__prop__ToProp__to_prop;
            bool_prop__from_bool Core__convert__Into__into;
            bool_prop__from_bool Core__convert__From__from;
            (* Transform inherent methods on Prop *)
            poly 2 Hax_lib__prop__Impl__and Hax_lib__prop__constructors__and;
            poly 2 Hax_lib__prop__Impl__or Hax_lib__prop__constructors__or;
            poly 1 Hax_lib__prop__Impl__not Hax_lib__prop__constructors__not;
            poly 2 Hax_lib__prop__Impl__eq Hax_lib__prop__constructors__eq;
            poly 2 Hax_lib__prop__Impl__ne Hax_lib__prop__constructors__ne;
            poly 2 Hax_lib__prop__Impl__implies
              Hax_lib__prop__constructors__implies;
            (* Transform standalone functions in `prop` *)
            poly 2 Hax_lib__prop__implies Hax_lib__prop__constructors__implies;
            poly 1 Hax_lib__prop__forall Hax_lib__prop__constructors__forall;
            poly 1 Hax_lib__prop__exists Hax_lib__prop__constructors__exists;
            (* Transform core `&`, `|`, `!` on `Prop` *)
            poly 2 Core__ops__bit__BitAnd__bitand
              Hax_lib__prop__constructors__and;
            poly 2 Core__ops__bit__BitOr__bitor Hax_lib__prop__constructors__or;
            poly 1 Core__ops__bit__Not__not Hax_lib__prop__constructors__not;
          ]

        let replacements = List.concat [ int_replacements; prop_replacements ]
      end

      module Error = Phase_utils.MakeError (struct
        let ctx = Diagnostics.Context.Phase phase_id
      end)

      module Attrs = Attr_payloads.Make (F) (Error)

      let visitor =
        object (self)
          inherit [_] Visitors.map as super

          method! visit_expr () e =
            match e.e with
            | App
                {
                  f = { e = GlobalVar f; _ } as f';
                  args = l;
                  trait;
                  generic_args;
                  bounds_impls;
                } -> (
                let l = List.map ~f:(self#visit_expr ()) l in
                let matching =
                  List.filter
                    (List.mapi ~f:(fun i x -> (i, x)) replacements)
                    ~f:(fun (_, { fn; args; ret; fn_replace = _ }) ->
                      Ast.Global_ident.eq_name fn f
                      && ret e.typ
                      &&
                      match List.for_all2 args l ~f:apply with
                      | Ok r -> r
                      | _ -> false)
                in
                match matching with
                | [ (_, { fn_replace; _ }) ] ->
                    let e =
                      fn_replace ~args:l ~typ:e.typ ~span:e.span ~generic_args
                        ~bounds_impls ~trait ~f:f'
                    in
                    self#visit_expr () e
                | [] -> (
                    (* In this case we need to avoid recursing again through the arguments *)
                    let visited =
                      let args = [] in
                      let e' =
                        App { f = f'; args; trait; generic_args; bounds_impls }
                      in
                      super#visit_expr () { e with e = e' }
                    in
                    match visited.e with
                    | App { f; trait; generic_args; bounds_impls; _ } ->
                        {
                          visited with
                          e =
                            App
                              { f; args = l; trait; generic_args; bounds_impls };
                        }
                    | _ -> super#visit_expr () e)
                | r ->
                    let msg =
                      "Found multiple matching patterns: "
                      ^ [%show: int list] (List.map ~f:fst r)
                    in
                    Stdio.prerr_endline msg;
                    U.Debug.expr e;
                    Error.assertion_failure e.span msg)
            | _ -> super#visit_expr () e
        end

      let ditems (l : A.item list) : B.item list =
        List.map ~f:(visitor#visit_item ()) l
    end)

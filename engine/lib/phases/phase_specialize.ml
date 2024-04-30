open! Prelude

module Make (F : Features.T) =
  Phase_utils.MakeMonomorphicPhase
    (F)
    (struct
      let phase_id = Diagnostics.Phase.Specialize

      module A = Ast.Make (F)
      module FB = F
      module B = Ast.Make (F)
      module U = Ast_utils.Make (F)
      module Visitors = Ast_visitors.Make (F)
      open A

      open struct
        open Concrete_ident_generated

        type pattern = {
          fn : name;
          fn_replace : name;
          args : (expr -> bool) list;
          ret : ty -> bool;
        }
        (** A pattern that helps matching against function applications *)

        type ('a, 'b) predicate = 'a -> 'b option
        (** Instead of working directly with boolean predicate, we
        work with `_ -> _ option` so that we can chain them *)

        (** Constructs a predicate out of predicates and names *)
        let mk (args : ('a, 'b) predicate list) (ret : ('c, 'd) predicate)
            (fn : name) (fn_replace : name) : pattern =
          let args = List.map ~f:(fun p x -> p x |> Option.is_some) args in
          let ret t = ret t |> Option.is_some in
          { fn; fn_replace; args; ret }

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
              name -> (Ast.Global_ident.t, Ast.Global_ident.t) predicate =
            eq ~eq:Ast.Global_ident.eq_name

          let erase : 'a. ('a, unit) predicate = fun _ -> Some ()

          let is_int : (ty, unit) predicate =
            tapp0 >>& eq_global_ident Hax_lib__int__Int >>& erase

          let any _ = Some ()
          let int_any = mk [ etyp >> is_int ] any
          let int_int_any = mk [ etyp >> is_int; etyp >> is_int ] any
          let any_int = mk [ any ] is_int
          let rint_any = mk [ etyp >> (tref >>& is_int) ] any

          let rint_rint_any =
            mk [ etyp >> (tref >>& is_int); etyp >> (tref >>& is_int) ] any

          let any_rint = mk [ any ] (tref >>& is_int)
        end

        (** The list of replacements *)
        let patterns =
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
            any_rint Hax_lib__int__Abstraction__lift
              Rust_primitives__hax__int__from_machine;
            int_any Hax_lib__int__Concretization__concretize
              Rust_primitives__hax__int__into_machine;
          ]
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
            | App { f = { e = GlobalVar f; _ } as f'; args = l; _ } -> (
                let l = List.map ~f:(self#visit_expr ()) l in
                let matching =
                  List.filter patterns ~f:(fun { fn; args; _ } ->
                      Ast.Global_ident.eq_name fn f
                      &&
                      match List.for_all2 args l ~f:apply with
                      | Ok r -> r
                      | _ -> false)
                in
                match matching with
                | [ { fn_replace; _ } ] ->
                    let f = Ast.Global_ident.of_name Value fn_replace in
                    let f = { f' with e = GlobalVar f } in
                    {
                      e with
                      e = App { f; args = l; impl = None; generic_args = [] };
                    }
                | [] -> super#visit_expr () e
                | _ ->
                    Error.assertion_failure e.span
                      "Found multiple matching patterns")
            | _ -> super#visit_expr () e
        end

      let ditems (l : A.item list) : B.item list =
        List.map ~f:(visitor#visit_item ()) l
    end)

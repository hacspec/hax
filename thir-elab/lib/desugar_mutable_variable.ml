open Base
open Ast
open Utils
module S = Set.M (LocalIdent)

class ['s] set_monoid =
  object
    inherit ['s] VisitorsRuntime.monoid
    method private zero = Set.empty (module LocalIdent)
    method private plus = Set.union
  end

let count (p : 'a pat) : local_ident list =
  (object
     inherit [_] pat_reduce as super
     inherit [_] set_monoid as m
     method visit_decorated _ _ _ { v } = super#visit_pat' () v

     method! visit_Binding _ _ _ var _ subpat =
       m#plus
         (Set.singleton (module LocalIdent) var)
         (Option.value_map subpat ~default:m#zero
            ~f:(fst >> super#visit_pat ()))
  end)
    #visit_pat
    () p
  |> Set.to_list

let dexpr (type mutable_variable)
    (e :
      (< mutable_reference : off
       ; mutable_pointer : off
       ; mutable_borrow : off
       ; mutable_variable : mutable_variable
       ; .. >
       as
       'a)
      expr) :
    < mutable_reference : off
    ; mutable_pointer : off
    ; mutable_borrow : off
    ; mutable_variable : off
    ; .. >
    expr =
  match e.v with
  | Borrow { kind = Mut _ } -> .
  | _ -> { v = Literal (String "x"); span = e.span; typ = Obj.magic () }

module Core.Iter.Traits.Iterator
open Rust_primitives

(*** Definition of the `iterator` trait *)
(** We define the types of the different method of the iterator trait
on their own. This is handy for revealing only certain fields of the
instances of the `iterator` trait. *)

unfold type t_next self item
  = self -> self * Core.Option.t_Option item
unfold type t_contains self item
  = self -> item -> Type0
unfold type t_fold self (item: Type0) (contains: t_contains self item)
  = #b:Type -> s:self -> b -> (b -> i:item{contains s i} -> b) -> b
unfold type t_enumerate self
  = self -> Core.Iter.Adapters.Enumerate.t_Enumerate self
unfold type t_step_by self
  = self -> usize -> Core.Iter.Adapters.Step_by.t_StepBy self
unfold type t_all self item
  = self -> (item -> bool) -> self * bool
unfold type t_rev self
  = self -> Core.Iter.Adapters.Rev.t_Rev self
unfold type t_map self item
  = #res: Type0 -> self -> (item -> res) -> Core.Iter.Adapters.Map.t_Map self (item -> res)
unfold type t_flat_map self item
  = #res: Type0 -> self -> (item -> res) -> Core.Iter.Adapters.Flatten.t_FlatMap self res (item -> res)
unfold type t_zip self
  = #other:Type0 -> self -> other -> Core.Iter.Adapters.Zip.t_Zip self other
unfold type t_take self
  = self -> usize -> Core.Iter.Adapters.Take.t_Take self

(* Inference behaves strangly with type synonyms... :( *)
// class iterator (self: Type) = {
//   f_Item: Type0;
//   f_next:      t_next      self f_Item;
//   f_contains:  t_contains  self f_Item; (* hax-specific method *)
//   f_fold:      t_fold      self f_Item f_contains;
//   f_enumerate: t_enumerate self;
// }

class iterator (self: Type u#0): Type u#1 = {
  [@@@FStar.Tactics.Typeclasses.no_method]
  f_Item: Type0;
  f_next:      self -> self * Core.Option.t_Option f_Item;
  f_contains:  self -> f_Item -> Type0;
  f_fold:      #b:Type0 -> s:self -> b -> (b -> i:f_Item{f_contains s i} -> b) -> b;
  f_enumerate: self -> Core.Iter.Adapters.Enumerate.t_Enumerate self;
  f_step_by:   self -> usize -> Core.Iter.Adapters.Step_by.t_StepBy self;
  f_all:       self -> (f_Item -> bool) -> self * bool;
  f_rev:       self -> Core.Iter.Adapters.Rev.t_Rev self;
  f_map:       #res: Type0 -> self -> (f_Item -> res) -> Core.Iter.Adapters.Map.t_Map self (f_Item -> res);
  f_flat_map:  #res: Type0 -> self -> (f_Item -> res) -> Core.Iter.Adapters.Flatten.t_FlatMap self res (f_Item -> res);
  f_zip:       #other:Type0 -> self -> other -> Core.Iter.Adapters.Zip.t_Zip self other;
  f_take:      self -> usize -> Core.Iter.Adapters.Take.t_Take self
}

let t_Iterator = iterator

assume val f_collect #i {|iterator i|} #t (x: i): t


[@FStar.Tactics.Typeclasses.tcinstance]
assume val take_iter (t: Type0) : Core.Iter.Traits.Iterator.iterator 
  (Core.Iter.Adapters.Take.t_Take t)

[@FStar.Tactics.Typeclasses.tcinstance]
assume val repeat_with_iter (t: Type0) : Core.Iter.Traits.Iterator.iterator 
  (Core.Iter.Sources.Repeat_with.t_RepeatWith t)

[@FStar.Tactics.Typeclasses.tcinstance]
assume val flat_map_iter (t: Type0) (u: Type0) (v: Type0) : Core.Iter.Traits.Iterator.iterator 
  (Core.Iter.Adapters.Flatten.t_FlatMap t u v)

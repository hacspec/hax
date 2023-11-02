module Core.Iter.Traits.Iterator

(*** Definition of the `iterator` trait *)
(** We define the types of the different method of the iterator trait
on their own. This is handy for revealing only certain fields of the
instances of the `iterator` trait. *)

unfold type t_next self item
  = self -> self * option item
unfold type t_contains self item
  = self -> item -> Type0
unfold type t_fold self (item: Type0) (contains: t_contains self item)
  = #b:Type -> s:self -> b -> (b -> i:item{contains s i} -> b) -> b
unfold type t_enumerate self
  = self -> Core.Iter.Adapters.Enumerate.t_Enumerate self
unfold type t_all self item
  = self -> (item -> bool) -> bool

(* Inference behaves strangly with type synonyms... :( *)
// class iterator (self: Type) = {
//   f_Item: Type;
//   f_next:      t_next      self f_Item;
//   f_contains:  t_contains  self f_Item; (* hax-specific method *)
//   f_fold:      t_fold      self f_Item f_contains;
//   f_enumerate: t_enumerate self;
// }

class iterator (self: Type) = {
  f_Item: Type;
  f_next:      self -> self * option f_Item;
  f_contains:  self -> f_Item -> Type0;
  f_fold:      #b:Type -> s:self -> b -> (b -> i:f_Item{f_contains s i} -> b) -> b;
  f_enumerate: self -> Core.Iter.Adapters.Enumerate.t_Enumerate self;
  f_all:       self -> (f_Item -> bool) -> bool
}


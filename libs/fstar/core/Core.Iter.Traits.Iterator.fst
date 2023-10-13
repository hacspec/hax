module Core.Iter.Traits.Iterator

(*** Definition of the `iterator` trait *)
(** We define the types of the different method of the iterator trait
on their own. This is handy for revealing only certain fields of the
instances of the `iterator` trait. *)

unfold type t_next self item
  = self -> self * option item
unfold type t_contains self item
  = self -> item -> Type0
unfold type t_fold self item (contains: t_contains self item)
  = #b:Type -> s:self -> b -> (b -> i:item{contains s i} -> b) -> b
unfold type t_enumerate self
  = self -> Core.Iter.Adapters.Enumerate.t_Enumerate self

class iterator self = {
  f_Item: Type;
  f_next:      t_next      self f_Item;
  f_contains:  t_contains  self f_Item; (* hax-specific method *)
  f_fold:      t_fold      self f_Item f_contains;
  f_enumerate: t_enumerate self;
}


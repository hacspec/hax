val count : 'a -> 'a list -> Z.t
val rev_acc : 'a list -> 'a list -> 'a list
val op_At : 'a list -> 'a list -> 'a list
val snoc : 'a list * 'a -> 'a list
val mapi_init : 'a -> 'b -> 'c -> 'd
val concatMap : ('a -> 'b list) -> 'a list -> 'b list
type ('a, 'b, 'c) memP = unit
val subset : 'a list -> 'a list -> bool
val noRepeats : 'a list -> bool
val assoc : 'a -> ('a * 'b) list -> 'b option
val unsnoc : 'a list -> 'a list * 'a
val split3 : 'a list -> Z.t -> 'a list * 'a * 'a list
val bool_of_compare : ('a -> 'b -> Z.t) -> 'a -> 'b -> bool
val compare_of_bool : ('a -> 'a -> bool) -> 'a -> 'a -> Z.t
val list_unref : 'a -> 'a
val list_ref : 'a -> 'b -> 'b
val list_refb : 'a -> 'b -> 'b
val isEmpty : 'a list -> bool
val singleton : 'a -> 'a list
val mem : 'a -> 'a list -> bool
val memT : 'a -> 'a list -> bool
val hd : 'a list -> 'a
val tl : 'a list -> 'a list
val tail : 'a list -> 'a list
val nth : 'a list -> Z.t -> 'a
val length : 'a list -> Z.t
val rev : 'a list -> 'a list
val map : ('a -> 'b) -> 'a list -> 'b list
val mapT : ('a -> 'b) -> 'a list -> 'b list
val mapi : (Z.t -> 'a -> 'b) -> 'a list -> 'b list
val map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
val map3 : ('a -> 'b -> 'c -> 'd) -> 'a list -> 'b list -> 'c list -> 'd list
val iter : ('a -> unit) -> 'a list -> unit
val iter2 : ('a -> 'b -> unit) -> 'a list -> 'b list -> unit
val iteri_aux : 'a -> 'b -> 'c -> 'd
val iteri : (Z.t -> 'a -> unit) -> 'a list -> unit
val partition : ('a -> bool) -> 'a list -> 'a list * 'a list
val append : 'a list -> 'a list -> 'a list
val rev_append : 'a list -> 'a list -> 'a list
val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
val fold_right : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
val fold_left2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b list -> 'c list -> 'a
val fold_right2 : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
val rev_map_onto : ('a -> 'b) -> 'a list -> 'b list -> 'b list
val init : 'a list -> 'a list
val last : 'a list -> 'a
val last_opt : 'a list -> 'a option
val collect : ('a -> 'b list) -> 'a list -> 'b list
val unzip : ('a * 'b) list -> 'a list * 'b list
val unzip3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list
val filter : ('a -> bool) -> 'a list -> 'a list
val sortWith : ('a -> 'a -> Z.t) -> 'a list -> 'a list
val for_all : ('a -> bool) -> 'a list -> bool
val forall2 : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
val tryFind : ('a -> bool) -> 'a list -> 'a option
val tryFindT : ('a -> bool) -> 'a list -> 'a option
val find : ('a -> bool) -> 'a list -> 'a option
val tryPick : ('a -> 'b option) -> 'a list -> 'b option
val flatten : 'a list list -> 'a list
val concat : 'a list list -> 'a list
val split : ('a * 'b) list -> 'a list * 'b list
val choose : ('a -> 'b option) -> 'a list -> 'b list
val existsb : ('a -> bool) -> 'a list -> bool
val existsML : ('a -> bool) -> 'a list -> bool
val contains : 'a -> 'a list -> bool
val zip : 'a list -> 'b list -> ('a * 'b) list
val splitAt : Z.t -> 'a list -> 'a list * 'a list
val filter_map : ('a -> 'b option) -> 'a list -> 'b list
val index : ('a -> bool) -> 'a list -> Z.t
val zip3 : 'a list -> 'b list -> 'c list -> ('a * 'b * 'c) list
val unique : ?eq:('a -> 'a -> bool) -> 'a list -> 'a list
val map_flatten : ('a -> 'b list) -> 'a list -> 'b list
val span : ('a -> bool) -> 'a list -> 'a list * 'a list

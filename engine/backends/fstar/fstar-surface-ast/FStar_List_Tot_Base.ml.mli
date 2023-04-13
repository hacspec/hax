val isEmpty : 'a list -> bool
val hd : 'a list -> 'a
val tail : 'a list -> 'a list
val tl : 'a list -> 'a list
val last : 'a list -> 'a
val init : 'a list -> 'a list
val length : 'a list -> Z.t
val nth : 'a list -> Z.t -> 'a option
val index : 'a list -> Z.t -> 'a
val count : 'a -> 'a list -> Z.t
val rev_acc : 'a list -> 'a list -> 'a list
val rev : 'a list -> 'a list
val append : 'a list -> 'a list -> 'a list
val op_At : 'a list -> 'a list -> 'a list
val snoc : 'a list * 'a -> 'a list
val flatten : 'a list list -> 'a list
val map : ('a -> 'b) -> 'a list -> 'b list
val mapi_init : 'a -> 'b -> 'c -> 'd
val mapi : (Z.t -> 'a -> 'b) -> 'a list -> 'b list
val concatMap : ('a -> 'b list) -> 'a list -> 'b list
val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
val fold_right : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
val fold_left2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b list -> 'c list -> 'a
val mem : 'a -> 'a list -> bool
type ('a, 'b, 'c) memP = unit
val contains : 'a -> 'a list -> bool
val existsb : ('a -> bool) -> 'a list -> bool
val find : ('a -> bool) -> 'a list -> 'a option
val filter : ('a -> bool) -> 'a list -> 'a list
val for_all : ('a -> bool) -> 'a list -> bool
val collect : ('a -> 'b list) -> 'a list -> 'b list
val tryFind : ('a -> bool) -> 'a list -> 'a option
val tryPick : ('a -> 'b option) -> 'a list -> 'b option
val choose : ('a -> 'b option) -> 'a list -> 'b list
val partition : ('a -> bool) -> 'a list -> 'a list * 'a list
val subset : 'a list -> 'a list -> bool
val noRepeats : 'a list -> bool
val assoc : 'a -> ('a * 'b) list -> 'b option
val split : ('a * 'b) list -> 'a list * 'b list
val unzip : ('a * 'b) list -> 'a list * 'b list
val unzip3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list
val splitAt : Z.t -> 'a list -> 'a list * 'a list
val unsnoc : 'a list -> 'a list * 'a
val split3 : 'a list -> Z.t -> 'a list * 'a * 'a list
val bool_of_compare : ('a -> 'b -> Z.t) -> 'a -> 'b -> bool
val compare_of_bool : ('a -> 'a -> bool) -> 'a -> 'a -> Z.t
val sortWith : ('a -> 'a -> Z.t) -> 'a list -> 'a list
val list_unref : 'a -> 'a
val list_ref : 'a -> 'b -> 'b
val list_refb : 'a -> 'b -> 'b

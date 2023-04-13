type heap = unit
type nonrec 'a ref = 'a ref
type ('a, 'b) mref = 'a ref
val emp : unit
val addr_of : 'a -> 'b
val is_mm : 'a -> 'b
type ('a, 'b, 'c, 'd) contains
type ('a, 'b) addr_unused_in
type ('a, 'b, 'c, 'd) unused_in
val fresh : 'a -> 'b -> 'c -> 'd
val sel : 'a -> 'b -> 'c
val upd : 'a -> 'b -> 'c -> 'd
val alloc : 'a -> 'b -> 'c -> 'd
val free_mm : 'a -> 'b -> 'c
val sel_tot : 'a -> 'b -> 'c
val upd_tot : 'a -> 'b -> 'c -> 'd
type aref = Ref of (unit * unit)
val dummy_aref : aref
val aref_of : 'a -> aref
val ref_of : 'a -> 'b -> 'c

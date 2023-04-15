val read : 'a ref -> 'a
val op_Bang : 'a ref -> 'a
val write : 'a ref -> 'a -> unit
val op_Colon_Equals : 'a ref -> 'a -> unit
val alloc : 'a -> 'a ref
val recall : 'a -> unit
val get : unit -> unit
type 'a witnessed = C
val gst_witness : 'a -> unit
val gst_recall : 'a -> unit

type ('a, 'b) mref = ('a, 'b) FStar_Monotonic_Heap.mref
type 'a ref = 'a FStar_Monotonic_Heap.ref
val ref_to_yojson : 'a -> 'b -> [> `Null ]
val ref_of_yojson : 'a -> 'b -> 'c
val read : 'a Stdlib.ref -> 'a
val op_Bang : 'a Stdlib.ref -> 'a
val write : 'a Stdlib.ref -> 'a -> unit
val op_Colon_Equals : 'a Stdlib.ref -> 'a -> unit
val alloc : 'a -> 'a Stdlib.ref
val recall : 'a -> unit
val get : unit -> unit
type 'a witnessed = 'a FStar_CommonST.witnessed
val gst_witness : 'a -> unit
val gst_recall : 'a -> unit

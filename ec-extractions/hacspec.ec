require import AllCore.
require export List.

theory Word.
  type t.

  op size : int.

  op ofint : int -> t.

  op ( + ) : t -> t -> t.
  op ( ^ ) : t -> t -> t.

  op rotate_left : t -> int -> t.
end Word.

clone export Word as WU8  with op size <= 1.
clone export Word as WU32 with op size <= 4.

theory Array.
  type element.
  type t.

  op size : int.

  op new : t.

  op "_.[_<-_]" : t -> int -> element -> t.
  op "_.[_]" : t -> int -> element.
end Array.

theory WordArray.
  clone Word.

  clone include Array with type element <- Word.t.

  op (+) : t -> t -> t.
  op (^) : t -> t -> t.

  op to_le_bytes : t -> WU8.t list.

  op from_seq_u32: WU32.t list -> t.

  op update_u8 : t -> int -> WU8.t list -> t.
  op update_u32 : t -> int -> WU32.t list -> t.
end WordArray.

theory ByteSeq.
  type t = WU8.t list.

  op new (i : int) : t =
    List.nseq i (WU8.ofint 0).

  op len (s : t) : int =
    List.size s.

  op num_exact_chunks : t -> int -> int.

  op get_exact_chunk : t -> int -> int -> t.

  op get_remainder_chunk : t -> int -> t.

  op set_exact_chunk : t -> int -> int -> t -> t.

  op set_chunk : t -> int -> int -> t -> t.
end ByteSeq.

theory Bytes.
  type t.

  op size : int.

  op new : t.

  op to_seq_u8 : t -> WU8.t list.

  op to_le_U32s : t -> WU32.t list.

  op from_seq_u8 : WU8.t list -> t.
  op from_seq_u32: WU32.t list -> t.

  op update : t -> int -> WU8.t list -> t.

  op slice : t -> int -> int -> WU8.t list.
end Bytes.

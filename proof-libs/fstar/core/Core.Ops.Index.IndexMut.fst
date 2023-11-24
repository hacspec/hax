module Core.Ops.Index.IndexMut


open LowStar.BufferOps
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST


class t_IndexMut t_Self t_Idx = {
  out_type: Type0;
  in_range: t_Self -> t_Idx -> Type0;
  f_index_mut: s:t_Self -> i:t_Idx{in_range s i} -> HST.St out_type;
}

open Rust_primitives
instance impl__index_mut_array t l n: t_IndexMut (t_Array t l) (int_t n)
  = { out_type = B.pointer t;
      in_range = (fun (s: t_Array t l) (i: int_t n) -> v i >= 0 && v i < v l);
      f_index_mut = (fun s i -> 
        admit ();
        B.sub s (cast i) 1ul
      );
    }

instance impl__index_mut_slice t n: t_IndexMut (t_Slice t) (int_t n)
  = { out_type = B.pointer t;
      in_range = (fun (s: t_Slice t) (i: int_t n) -> v i >= 0 && v i < v (spec_length s));
      f_index_mut = (fun (Some s) i -> 
        admit ();
        B.sub s.buffer (cast i) 1ul
      );
    }


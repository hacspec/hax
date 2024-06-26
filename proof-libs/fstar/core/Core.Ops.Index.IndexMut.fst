module Core.Ops.Index.IndexMut

class t_IndexMut #t_Self #t_Idx = {
  f_Input: Type0;
  in_range: t_Self -> t_Idx -> Type0;
  f_index_mut: s:t_Self -> i:t_Idx{in_range s i} -> v:f_Input -> t_Self;
}

open Rust_primitives
instance impl__index_mut t l n: t_IndexMut #(t_Array t l) #(int_t n)
  = { f_Input = t;
      in_range = (fun (s: t_Array t l) (i: int_t n) -> v i >= 0 && v i < v l);
      f_index_mut = (fun s i x -> Seq.upd s (v i) x);
    }

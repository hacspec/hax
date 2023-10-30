module Core.Ops.Index

class t_Index t_Self t_Idx = {
  f_Output: Type;
  in_range: t_Self -> t_Idx -> Type0;
  f_index: s:t_Self -> i:t_Idx{in_range s i} -> f_Output;
}

open Rust_primitives
instance impl__index t l n: t_Index (t_Array t l) (int_t n)
  = { f_Output = t;
      in_range = (fun (s: t_Array t l) (i: int_t n) -> v i >= 0 && v i < v l);
      f_index = (fun s i -> Seq.index s (v i));
    }

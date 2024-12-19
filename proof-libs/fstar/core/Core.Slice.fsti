module Core.Slice
open Rust_primitives.Arrays
open Rust_primitives.Integers

let impl__len (#t: Type) (s: t_Slice t)
  : len: usize {len == sz (Seq.length s)} = 
  sz (Seq.length s)

open Core.Slice.Iter

val impl__chunks #a (x: t_Slice a) (cs: usize): t_Chunks a

let impl__iter #t (s: t_Slice t): t_Slice t = s

val impl__chunks_exact #a (x: t_Slice a) (cs: usize):
    Pure (t_Slice (t_Slice a))
    (requires True)
    (ensures (fun r -> forall i. i < v (length x) ==> length x ==  cs))

open Core.Ops.Index

instance impl__index t n: t_Index (t_Slice t) (int_t n)
  = { f_Output = t;
      f_index_pre = (fun (s: t_Slice t) (i: int_t n) -> v i >= 0 && v i < v (length s));
      f_index_post = (fun _ _ _ -> true);
      f_index = (fun s i -> Seq.index s (v i));
    }

let impl__copy_from_slice #t (x: t_Slice t) (y:t_Slice t) : t_Slice t = y

val impl__split_at #t (s: t_Slice t) (mid: usize): Pure (t_Slice t * t_Slice t)
    (requires (v mid <= Seq.length s))
    (ensures (fun (x,y) -> Seq.length x == v mid /\ Seq.length y == Seq.length s - v mid /\
                        x == Seq.slice s 0 (v mid) /\ y == Seq.slice s (v mid) (Seq.length s) /\
                        s == Seq.append x y))

let impl__is_empty (s: t_Slice 'a): bool = Seq.length s = 0

let impl__clone_from_slice #t (x:t_Slice t) = x

let impl__into_vec #t (x:t_Slice t) = x

module Rust_primitives.Slice

open FStar.Mul
open Rust_primitives.Arrays
open Rust_primitives.Integers

let slice_length (#a: Type) (s: t_Slice a): res: usize {res == sz (Seq.length s)} = sz (Seq.length s)
let slice_split_at (#v_T: Type0) (s: t_Slice v_T) (mid: usize {mid <=. length s}): t_Slice v_T & t_Slice v_T = 
  Seq.slice s 0 (v mid), Seq.slice s (v mid) (Seq.length s)
let slice_contains (#a: eqtype) (s: t_Slice a) (v: a): bool = Seq.mem v s
let slice_index (#t: Type) (s: t_Slice t) (i: usize {i <. length s}): t = Seq.index s (v i)
let slice_slice (#v_T: Type0) (s: t_Slice v_T) (start: usize {start <=. length s}) (end_: usize {start <=. end_ /\ end_ <=. length s}): t_Slice v_T =
  Seq.slice s (v start) (v end_)
let slice_clone_from_slice (#v_T: Type0) (s: t_Slice v_T) (src: t_Slice v_T {slice_length src == slice_length s}): t_Slice v_T = src
let slice_copy_within (#v_T: Type0) (s: t_Slice v_T)
  (start: usize) (end_: usize {start <=. end_ /\ end_ <=. length s})
  (dest: usize {v dest <= Seq.length s - (v end_ - v start)}): t_Slice v_T =
  Seq.append (Seq.slice s 0 (v dest))
    (Seq.append (Seq.slice s (v start) (v end_))
      (Seq.slice s (v dest + (v end_ - v start)) (Seq.length s)))
val array_map (#t: Type) (#u: Type) (l: usize) (#ft: Type)
  (s: t_Array t l) (f: t -> u): res: t_Array u l {forall i. Seq.index res i == f (Seq.index s i)}
let array_as_slice (#t: Type) (l: usize) (s: t_Array t l): t_Slice t =
  s
let array_slice (#t: Type) (l: usize) (s: t_Array t l) = slice_slice s
val array_from_fn (#t: Type) (len: usize) (#ft: Type) (f: (x: usize {x <. len}) -> t): 
  Pure (t_Array t len) (requires True) (ensures (fun a -> forall i. Seq.index a i == f (sz i)))
let array_index (#t: Type) (l: usize) (s: t_Array t l) (i: usize {i <. length s}): t = Seq.index s (v i)
let slice_empty (#t: Type) (): t_Slice t = Seq.empty
let array_from_ref (#t: Type) (x: t): t_Array t (mk_usize 1) = Seq.create 1 x

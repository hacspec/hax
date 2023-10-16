module Core.Ops.Range
open Rust_primitives

type t_RangeTo   (t: Type) = {f_end: t}
type t_RangeFrom (t: Type) = {f_start: t}
type t_Range     (t: Type) = {f_start: t; f_end: t}

open Core.Iter.Traits.Iterator

let rec fold_range' #t
  (min: Rust_primitives.int_t t) (max: Rust_primitives.int_t t {v min <= v max})
  (init: 'a) (f: ('a -> i:Rust_primitives.int_t t{v i < v max /\ v i >= v min} -> 'a))
  : Tot 'a (decreases (v max - v min))
  = if min = max
    then init
    else fold_range' (add min (Rust_primitives.mk_int 1)) max (f init min) f

val iterator_range_enumerate t: t_enumerate (t_Range (Rust_primitives.int_t t))

instance iterator_range t: iterator (t_Range (Rust_primitives.int_t t)) = 
  { f_Item = Rust_primitives.int_t t;
    f_next = (fun {f_start; f_end} -> 
       if f_start >=. f_end then ({f_start; f_end}, None)
       else ({f_start = f_start +. Rust_primitives.mk_int 0; f_end}, Some f_start)
    );
    f_contains = (fun x i -> v i < v x.f_end /\ v i >= v x.f_start);
    f_fold = (fun #b r init f ->  if r.f_start >=. r.f_end then init
                             else fold_range' r.f_start r.f_end init (fun x i -> f x i));
    f_enumerate = iterator_range_enumerate t;
  }

open Core.Ops.Index

instance impl_range_index_slice t len n : t_Index (t_Array t len) (t_Range (int_t n)) = {
  f_Output = t_Slice t;
  in_range = (fun (arr: t_Array t len) {f_start; f_end} -> 
    v f_start >= 0     /\
    v f_start <= v len /\
    v f_end   <= v len
  );
  f_index = (fun arr {f_start; f_end} -> 
      if f_start <. f_end
      then Seq.slice arr (v f_start) (v f_end)
      else Seq.empty
    );
}

instance impl_index_range_array t n : t_Index (t_Slice t) (t_Range (int_t n)) = {
  f_Output = t_Slice t;
  in_range = (fun (s: t_Slice t) {f_start; f_end} -> 
    let len = Rust_primitives.length s in
    v f_start >= 0     /\
    v f_start <= v len /\
    v f_end   <= v len
  );
  f_index = (fun s {f_start; f_end} -> 
      if f_start <. f_end
      then Seq.slice s (v f_start) (v f_end)
      else Seq.empty
    );
}

(*

module RangeTo = Core.Ops.Range.RangeTo

instance rangeTo_index t len : index (array t len) RangeTo.range = {
  output = slice t;
  in_range = (fun (arr: array t len) { RangeTo.f_end } -> 
    v f_end   <= Seq.length arr
  );
  (.[]) = (fun arr { f_end } -> 
      Seq.slice arr 0 (v f_end)
    );
}

module RangeFrom = Core.Ops.Range.RangeFrom

instance rangeFrom_index t len : index (array t len) RangeFrom.range = {
  output = slice t;
  in_range = (fun (arr: array t len) { RangeFrom.f_start } -> 
    v f_start < v len
  );
  (.[]) = (fun arr { f_start } -> 
      Seq.slice arr (v f_start) (Seq.length arr)
    );
}

instance rangeFrom_index_slice_usize t : index (slice t) usize = magic ()

instance rangeFrom_index_slice t : index (slice t) RangeFrom.range = {
  output = slice t;
  in_range = (fun (arr: slice t) { RangeFrom.f_start } -> 
    v f_start < Seq.length arr
  );
  (.[]) = (fun arr { f_start } -> 
      Seq.slice arr (v f_start) (Seq.length arr)
    );
}

*)

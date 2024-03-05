module Core.Ops.Range
open Rust_primitives

type t_RangeTo   (t: Type) = {f_end: t}
type t_RangeFrom (t: Type) = {f_start: t}
type t_Range     (t: Type) = {f_start: t; f_end: t}
type t_RangeFull           = | RangeFull

open Core.Iter.Traits.Iterator
module LI = Lib.IntTypes

let rec fold_range' #t 
  (min: Rust_primitives.pub_int_t t) (max: Rust_primitives.pub_int_t t{v min <= v max})
  (init: 'a) (f: ('a -> i:Rust_primitives.pub_int_t t{v i < v max /\ v i >= v min} -> 'a))
  : Tot 'a (decreases (v max - v min))
  = if min =. max
    then init
    else fold_range' (add min (Rust_primitives.mk_int_l #_ #LI.PUB 1)) max (f init min) f

val iterator_range_enumerate t: t_enumerate (t_Range (Rust_primitives.pub_int_t t))
val iterator_range_step_by t: t_step_by (t_Range (Rust_primitives.pub_int_t t))
val iterator_range_all t: t_all (t_Range (Rust_primitives.pub_int_t t)) (Rust_primitives.pub_int_t t)

instance iterator_range t: iterator (t_Range (Rust_primitives.pub_int_t t)) = 
  { f_Item = Rust_primitives.pub_int_t t;
    f_next = (fun {f_start; f_end} -> 
       if f_start >=. f_end then ({f_start; f_end}, None)
       else ({f_start = f_start +. Rust_primitives.mk_pub_int 0; f_end}, Some f_start)
    );
    f_contains = (fun x i -> v i < v x.f_end /\ v i >= v x.f_start);
    f_fold = (fun #b r init f ->  if r.f_start >=. r.f_end then init
                               else fold_range' r.f_start r.f_end init (fun x i -> f x i));
    f_enumerate = iterator_range_enumerate t;
    f_step_by = iterator_range_step_by t;
    f_all = iterator_range_all t;
  }

open Core.Ops.Index

instance impl_index_range_slice t n : t_Index (t_Slice t) (t_Range (pub_int_t n)) 
  = { f_Output = t_Slice t
    ; in_range = (fun (s: t_Slice t) {f_start; f_end} -> 
         let len = Rust_primitives.length s in
         v f_start >= 0 /\ v f_start <= v len /\ v f_end <= v len)
    ; f_index = (fun s {f_start; f_end} -> 
          if f_start <. f_end then Seq.slice s (v f_start) (v f_end)
                              else Seq.empty)}

instance impl_index_range_to_slice t n : t_Index (t_Slice t) (t_RangeTo (pub_int_t n)) 
  = { f_Output = t_Slice t
    ; in_range = (fun (s: t_Slice t) ({f_end}: t_RangeTo (pub_int_t n)) -> 
         let len = Rust_primitives.length s in v f_end <= v len)
    ; f_index = (fun s {f_end} -> if 0 < v f_end then Seq.slice s 0 (v f_end) else Seq.empty)}

instance impl_index_range_from_slice t n : t_Index (t_Slice t) (t_RangeFrom (pub_int_t n)) 
  = { f_Output = t_Slice t
    ; in_range = (fun (s: t_Slice t) ({f_start}: t_RangeFrom (pub_int_t n)) -> 
         let len = Rust_primitives.length s in v f_start >= 0 /\ v f_start <= v len)
    ; f_index = (fun s {f_start} -> 
         let len = Rust_primitives.length s in
         if v f_start = v len then Seq.empty else Seq.slice s (v f_start) (v len))}
         
instance impl_index_range_full_slice t : t_Index (t_Slice t) t_RangeFull
  = { f_Output = t_Slice t
    ; in_range = (fun (s: t_Slice t) _ -> True)
    ; f_index = (fun s _ -> s)}

instance impl_range_index_array t len n : t_Index (t_Array t len) (t_Range (pub_int_t n)) = 
  let i = impl_index_range_slice t n in
  { f_Output = i.f_Output
  ; in_range = (fun (s: t_Array t len) r -> i.in_range s r)
  ; f_index = (fun s r -> i.f_index s r) }
  
instance impl_range_to_index_array t len n : t_Index (t_Array t len) (t_RangeTo (pub_int_t n)) = 
  let i = impl_index_range_to_slice t n in
  { f_Output = i.f_Output
  ; in_range = (fun (s: t_Array t len) r -> i.in_range s r)
  ; f_index = (fun s r -> i.f_index s r) }

instance impl_range_from_index_array t len n : t_Index (t_Array t len) (t_RangeFrom (pub_int_t n)) = 
  let i = impl_index_range_from_slice t n in
  { f_Output = i.f_Output
  ; in_range = (fun (s: t_Array t len) r -> i.in_range s r)
  ; f_index = (fun s r -> i.f_index s r) }

instance impl_range_full_index_array t len : t_Index (t_Array t len) t_RangeFull = 
  let i = impl_index_range_full_slice t in
  { f_Output = i.f_Output
  ; in_range = (fun (s: t_Array t len) r -> i.in_range s r)
  ; f_index = (fun s r -> i.f_index s r) }

open Rust_primitives.Hax

let update_at_tc_array_range_super t l n: t_Index (t_Array t l) (t_Range (pub_int_t n))
  = FStar.Tactics.Typeclasses.solve
let update_at_tc_array_range_to_super t l n: t_Index (t_Array t l) (t_RangeTo (pub_int_t n))
  = FStar.Tactics.Typeclasses.solve
let update_at_tc_array_range_from_super t l n: t_Index (t_Array t l) (t_RangeFrom (pub_int_t n))
  = FStar.Tactics.Typeclasses.solve
let update_at_tc_array_range_full_super t l: t_Index (t_Array t l) t_RangeFull
  = FStar.Tactics.Typeclasses.solve

val update_at_array_range t l n
  (s: t_Array t l) (i: t_Range (pub_int_t n) {(update_at_tc_array_range_super t l n).in_range s i})
  : (update_at_tc_array_range_super t l n).f_Output -> t_Array t l
val update_at_array_range_to t l n
  (s: t_Array t l) (i: t_RangeTo (pub_int_t n) {(update_at_tc_array_range_to_super t l n).in_range s i})
  : (update_at_tc_array_range_to_super t l n).f_Output -> t_Array t l
val update_at_array_range_from t l n
  (s: t_Array t l) (i: t_RangeFrom (pub_int_t n) {(update_at_tc_array_range_from_super t l n).in_range s i})
  : (update_at_tc_array_range_from_super t l n).f_Output -> t_Array t l
val update_at_array_range_full t l
  (s: t_Array t l) (i: t_RangeFull)
  : (update_at_tc_array_range_full_super t l).f_Output -> t_Array t l

instance update_at_tc_array_range t l n: update_at_tc (t_Array t l) (t_Range (pub_int_t n)) = {
  super_index = update_at_tc_array_range_super t l n;
  update_at = update_at_array_range t l n
}
instance update_at_tc_array_range_to t l n: update_at_tc (t_Array t l) (t_RangeTo (pub_int_t n)) = {
  super_index = update_at_tc_array_range_to_super t l n;
  update_at = update_at_array_range_to t l n
}
instance update_at_tc_array_range_from t l n: update_at_tc (t_Array t l) (t_RangeFrom (pub_int_t n)) = {
  super_index = update_at_tc_array_range_from_super t l n;
  update_at = update_at_array_range_from t l n
}
instance update_at_tc_array_range_full t l: update_at_tc (t_Array t l) t_RangeFull = {
  super_index = update_at_tc_array_range_full_super t l;
  update_at = update_at_array_range_full t l
}

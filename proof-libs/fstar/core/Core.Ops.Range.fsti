module Core.Ops.Range
open Rust_primitives

inline_for_extraction
type t_RangeTo   (t: Type) = {f_end: t}
inline_for_extraction
type t_RangeFrom (t: Type) = {f_start: t}
inline_for_extraction
type t_Range     (t: Type) = {f_start: t; f_end: t}
inline_for_extraction
type t_RangeFull           = | RangeFull

open Core.Iter.Traits.Iterator

open LowStar.BufferOps
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST


let rec fold_range' #t
  (min: Rust_primitives.int_t t) (max: Rust_primitives.int_t t {v min <= v max})
  (init: 'a) (f: ('a -> i:Rust_primitives.int_t t{v i < v max /\ v i >= v min} -> HST.St 'a))
  : HST.St 'a (decreases (v max - v min))
  = if min = max
    then init
    else fold_range' (add min (Rust_primitives.mk_int 1)) max (f init min) f

inline_for_extraction
val iterator_range_enumerate t: t_enumerate (t_Range (Rust_primitives.int_t t))
inline_for_extraction
val iterator_range_step_by t: t_step_by (t_Range (Rust_primitives.int_t t))
inline_for_extraction
val iterator_range_all t: t_all (t_Range (Rust_primitives.int_t t)) (Rust_primitives.int_t t)

inline_for_extraction
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
    f_step_by = iterator_range_step_by t;
    f_all = iterator_range_all t;
  }

open Core.Ops.Index

inline_for_extraction
instance impl_index_range_slice t n : t_Index (t_Slice t) (t_Range (int_t n)) 
  = { f_Output = t_Slice t
    ; in_range = (fun (s: t_Slice t) {f_start; f_end} -> 
         let len = Rust_primitives.spec_length s in
         v f_start >= 0 /\ v f_start <= v len /\ v f_end <= v len)
    ; f_index = (fun s r ->
            admit ();
            let len = r.f_end -. r.f_start in
            let subbuf: B.buffer t = B.sub s.buffer (cast r.f_start) len in
            {buffer = subbuf; len} <: t_Slice t
          )
       }

inline_for_extraction
instance impl_index_range_to_slice t n : t_Index (t_Slice t) (t_RangeTo (int_t n)) 
  = { f_Output = t_Slice t
    ; in_range = (fun (s: t_Slice t) (r:t_RangeTo (int_t n)) -> 
         let len = Rust_primitives.spec_length s in
         v r.f_end <= v len)
    ; f_index = (fun s (r:t_RangeTo (int_t n)) ->
            admit ();
            let len = r.f_end in
            let subbuf: B.buffer t = B.sub s.buffer 0ul len in
            {buffer = subbuf; len} <: t_Slice t
          )
       }

inline_for_extraction
instance impl_index_range_from_slice t n : t_Index (t_Slice t) (t_RangeFrom (int_t n)) 
  = { f_Output = t_Slice t
    ; in_range = (fun (s: t_Slice t) (r:t_RangeFrom (int_t n)) -> 
         let len = Rust_primitives.spec_length s in
         v r.f_start >= 0 /\ v r.f_start <= v len)
    ; f_index = (fun s (r:t_RangeFrom (int_t n)) ->
            admit ();
            let len = s.len -. r.f_start in
            let subbuf: B.buffer t = B.sub s.buffer (cast r.f_start) len in
            {buffer = subbuf; len} <: t_Slice t
          )
       }

inline_for_extraction
instance impl_index_range_full_slice t : t_Index (t_Slice t) (t_RangeFull) 
  = { f_Output = t_Slice t
    ; in_range = (fun (s: t_Slice t) (r:t_RangeFull) -> True)
    ; f_index = (fun s (r:t_RangeFull) ->
            s)
}

inline_for_extraction
instance impl_range_index_array t len n : t_Index (t_Array t len) (t_Range (int_t n)) = 
  { f_Output = t_Slice t
  ; in_range = (fun (s: t_Array t len) (r:t_Range (int_t n)) -> True)
  ; f_index = (fun s r ->
            let len = r.f_end -. r.f_start in
            let subbuf: B.buffer t = B.sub s (cast r.f_start) len in
            {buffer=subbuf;len=len})
  }
  
inline_for_extraction
instance impl_range_to_index_array t len n : t_Index (t_Array t len) (t_RangeTo (int_t n)) = 
  { f_Output = t_Slice t
  ; in_range = (fun (s: t_Array t len) (r:t_RangeTo (int_t n)) -> True)
  ; f_index = (fun s (r:t_RangeTo (int_t n)) ->
            let len = r.f_end in
            let subbuf: B.buffer t = B.sub s 0ul len in
            {buffer=subbuf;len=len})
  }

inline_for_extraction
instance impl_range_from_index_array t len n : t_Index (t_Array t len) (t_RangeFrom (int_t n)) = 
  { f_Output = t_Slice t
  ; in_range = (fun (s: t_Array t len) (r:t_RangeFrom (int_t n)) -> True)
  ; f_index = (fun s (r:t_RangeFrom (int_t n)) ->
            let len = len -. r.f_start in
            let subbuf: B.buffer t = B.sub s r.f_start len in
            {buffer=subbuf;len=len})
}

inline_for_extraction
instance impl_range_full_index_array t len : t_Index (t_Array t len) t_RangeFull = 
  { f_Output = t_Slice t
  ; in_range = (fun (s: t_Array t len) (r:t_RangeFull) -> True)
  ; f_index = (fun s (r:t_RangeFull) ->
            let len = len in
            let subbuf: B.buffer t = B.sub s 0ul len in
            {buffer=subbuf;len=len})
}

open Rust_primitives.Hax

inline_for_extraction
let update_at_tc_array_range_super t l n: t_Index (t_Array t l) (t_Range (int_t n))
  = FStar.Tactics.Typeclasses.solve
inline_for_extraction
let update_at_tc_array_range_to_super t l n: t_Index (t_Array t l) (t_RangeTo (int_t n))
  = FStar.Tactics.Typeclasses.solve
inline_for_extraction
let update_at_tc_array_range_from_super t l n: t_Index (t_Array t l) (t_RangeFrom (int_t n))
  = FStar.Tactics.Typeclasses.solve
inline_for_extraction
let update_at_tc_array_range_full_super t l n: t_Index (t_Array t l) t_RangeFull
  = FStar.Tactics.Typeclasses.solve

inline_for_extraction
val update_at_array_range t l n
  (s: t_Array t l) (i: t_Range (int_t n) {(update_at_tc_array_range_super t l n).in_range s i})
  : (update_at_tc_array_range_super t l n).f_Output -> t_Array t l
inline_for_extraction
val update_at_array_range_to t l n
  (s: t_Array t l) (i: t_RangeTo (int_t n) {(update_at_tc_array_range_to_super t l n).in_range s i})
  : (update_at_tc_array_range_to_super t l n).f_Output -> t_Array t l
inline_for_extraction
val update_at_array_range_from t l n
  (s: t_Array t l) (i: t_RangeFrom (int_t n) {(update_at_tc_array_range_from_super t l n).in_range s i})
  : (update_at_tc_array_range_from_super t l n).f_Output -> t_Array t l
inline_for_extraction
val update_at_array_range_full t l n
  (s: t_Array t l) (i: t_RangeFull)
  : (update_at_tc_array_range_full_super t l n).f_Output -> t_Array t l

// <<<<<<< updated upstream
// instance update_at_tc_array_range t l n: update_at_tc (t_Array t l) (t_Range (int_t n)) = {
//   super_index = update_at_tc_array_range_super t l n;
//   update_at = update_at_array_range t l n
// }
// instance update_at_tc_array_range_to t l n: update_at_tc (t_Array t l) (t_RangeTo (int_t n)) = {
//   super_index = update_at_tc_array_range_to_super t l n;
//   update_at = update_at_array_range_to t l n
// }
// instance update_at_tc_array_range_from t l n: update_at_tc (t_Array t l) (t_RangeFrom (int_t n)) = {
//   super_index = update_at_tc_array_range_from_super t l n;
//   update_at = update_at_array_range_from t l n
// }
// instance update_at_tc_array_range_full t l n: update_at_tc (t_Array t l) t_RangeFull = {
//   super_index = update_at_tc_array_range_full_super t l n;
//   update_at = update_at_array_range_full t l n
// }
// ||||||| Stash base
// instance update_at_tc_array_range t l n: update_at_tc (t_Array t l) (t_Range (int_t n)) = {
//   super_index = update_at_tc_array_range_super t l n;
//   update_at = update_at_array_range t l n
// }
// instance update_at_tc_array_range_to t l n: update_at_tc (t_Array t l) (t_RangeTo (int_t n)) = {
//   super_index = update_at_tc_array_range_to_super t l n;
//   update_at = update_at_array_range_to t l n
// }
// instance update_at_tc_array_range_from t l n: update_at_tc (t_Array t l) (t_RangeFrom (int_t n)) = {
//   super_index = update_at_tc_array_range_from_super t l n;
//   update_at = update_at_array_range_from t l n
// }
// =======
// // instance update_at_tc_array_range t l n: update_at_tc (t_Array t l) (t_Range (int_t n)) = {
// //   super_index = update_at_tc_array_range_super t l n;
// //   update_at = update_at_array_range t l n
// // }
// // instance update_at_tc_array_range_to t l n: update_at_tc (t_Array t l) (t_RangeTo (int_t n)) = {
// //   super_index = update_at_tc_array_range_to_super t l n;
// //   update_at = update_at_array_range_to t l n
// // }
// // instance update_at_tc_array_range_from t l n: update_at_tc (t_Array t l) (t_RangeFrom (int_t n)) = {
// //   super_index = update_at_tc_array_range_from_super t l n;
// //   update_at = update_at_array_range_from t l n
// // }
// >>>>>>> Stashed changes


open Rust_primitives.Integers

inline_for_extraction
instance impl__index_mut_array_range t l n: t_IndexMut (t_Array t l) (t_Range (int_t n))
  = { out_type = t_Slice t;
      in_range = (fun (s: t_Array t l) (i: t_Range (int_t n)) -> True);
      f_index_mut = (fun s r ->
           let f_start = r.f_start in
           let f_end = r.f_end in
           assume (v f_end > v f_start);
           let len = f_end -! f_start in
           let buffer = B.sub s f_start len in
           {buffer; len});
    }

inline_for_extraction
instance impl__index_mut_array_range_from t l n: t_IndexMut (t_Array t l) (t_RangeFrom (int_t n))
  = { out_type = t_Slice t;
      in_range = (fun (s: t_Array t l) (i: t_RangeFrom (int_t n)) -> True);
      f_index_mut = (fun s r -> 
           let f_start = r.f_start in
           let f_end = l in
           let len =  f_end -! f_start in
           let buffer = B.sub s f_start len in
           {buffer; len});
    }

inline_for_extraction
instance impl__index_mut_array_range_to t l n: t_IndexMut (t_Array t l) (t_RangeTo (int_t n))
  = { out_type = t_Slice t;
      in_range = (fun (s: t_Array t l) (i: t_RangeTo (int_t n)) -> True);
      f_index_mut = (fun s r -> 
           let f_end = r.f_end in
           let len = f_end in
           let buffer = B.sub s 0ul len in
           {buffer; len});
    }

inline_for_extraction
instance impl__index_mut_slice t n: t_IndexMut (t_Slice t) (t_Range (int_t n))
  = { out_type = t_Slice t;
      in_range = (fun (s: t_Slice t) (i: t_Range (int_t n)) -> True);
      f_index_mut = (fun s {f_start; f_end} -> 
           if f_end >=. f_start
           then
             ( admit ();
               let len = f_end -! f_start in
               let buffer = B.sub s.buffer f_start len in
               {buffer; len})
           else admit()
      );
    }

module Core.Ops.Range
open Rust_primitives

type t_RangeTo   (t: Type) = {f_end: t}
type t_RangeFrom (t: Type) = {f_start: t}
type t_Range     (t: Type) = {f_start: t; f_end: t}
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

val iterator_range_enumerate t: t_enumerate (t_Range (Rust_primitives.int_t t))
val iterator_range_step_by t: t_step_by (t_Range (Rust_primitives.int_t t))
val iterator_range_all t: t_all (t_Range (Rust_primitives.int_t t)) (Rust_primitives.int_t t)

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

instance impl_index_range_slice t n : t_Index (t_Slice t) (t_Range (int_t n)) 
  = { f_Output = t_Slice t
    ; in_range = (fun (s: t_Slice t) {f_start; f_end} -> 
         let len = Rust_primitives.spec_length s in
         v f_start >= 0 /\ v f_start <= v len /\ v f_end <= v len)
    ; f_index = (fun s {f_start; f_end} -> 
          if f_start <. f_end 
          then
            let len = f_end -. f_start in
            let s = s in
            admit ();
            let buffer: B.buffer t = B.sub s.buffer (cast f_start) (Ghost.hide (cast len)) in
            let len: B.buffer usize = B.alloca (cast len <: usize) 1ul in
            {buffer; len}
          else admit()
          )
       }

instance impl_index_range_to_slice t n : t_Index (t_Slice t) (t_RangeTo (int_t n)) 
  = { f_Output = t_Slice t
    ; in_range = (fun (s: t_Slice t) ({f_end}: t_RangeTo (int_t n)) -> 
         let len = Rust_primitives.spec_length s in v f_end <= v len)
    ; f_index = admit ()}
    // ; f_index = (fun s {f_end} -> if 0 < v f_end then Seq.slice s 0 (v f_end) else Seq.empty)}

instance impl_index_range_from_slice t n : t_Index (t_Slice t) (t_RangeFrom (int_t n)) 
   = admit ()
//   = { f_Output = t_Slice t
//     ; in_range = (fun (s: t_Slice t) ({f_start}: t_RangeFrom (int_t n)) -> 
// <<<<<<< Updated upstream
//          let len = Rust_primitives.length s in v f_start >= 0 /\ v f_start <= v len)
//     ; f_index = (fun s {f_start} -> 
//          let len = Rust_primitives.length s in
//          if v f_start = v len then Seq.empty else Seq.slice s (v f_start) (v len))}
         
instance impl_index_range_full_slice t : t_Index (t_Slice t) t_RangeFull
         = admit ()
//   = { f_Output = t_Slice t
//     ; in_range = (fun (s: t_Slice t) _ -> True)
//     ; f_index = (fun s _ -> s)}
// ||||||| Stash base
//          let len = Rust_primitives.length s in v f_start >= 0 /\ v f_start <= v len)
//     ; f_index = (fun s {f_start} -> 
//          let len = Rust_primitives.length s in
//          if v f_start = v len then Seq.empty else Seq.slice s (v f_start) (v len))}
// =======
//          let len = Rust_primitives.spec_length s in v f_start >= 0 /\ v f_start <= v len)
//     // ; f_index = (fun s {f_start} -> 
//     ; f_index = (fun s {f_start} -> admit ())}
//     //      let len = Rust_primitives.spec_length s in
//     //      if v f_start = v len then Seq.empty else Seq.slice s (v f_start) (v len))}
// >>>>>>> Stashed changes

instance impl_range_index_array t len n : t_Index (t_Array t len) (t_Range (int_t n)) = 
  let i = impl_index_range_slice t n in
  admit ()
  // { f_Output = i.f_Output
  // ; in_range = (fun (s: t_Array t len) r -> i.in_range s r)
  // ; f_index = (fun s r -> i.f_index s r) }
  
instance impl_range_to_index_array t len n : t_Index (t_Array t len) (t_RangeTo (int_t n)) = 
  let i = impl_index_range_to_slice t n in
  admit ()
  // { f_Output = i.f_Output
  // ; in_range = (fun (s: t_Array t len) r -> i.in_range s r)
  // ; f_index = (fun s r -> i.f_index s r) }

instance impl_range_from_index_array t len n : t_Index (t_Array t len) (t_RangeFrom (int_t n)) = 
  admit ()
  // let i = impl_index_range_from_slice t n in
  // { f_Output = i.f_Output
  // ; in_range = (fun (s: t_Array t len) r -> i.in_range s r)
  // ; f_index = (fun s r -> i.f_index s r) }

instance impl_range_full_index_array t len : t_Index (t_Array t len) t_RangeFull = 
  let i = impl_index_range_full_slice t in
  admit ()
  // { f_Output = i.f_Output
  // ; in_range = (fun (s: t_Array t len) r -> i.in_range s r)
  // ; f_index = (fun s r -> i.f_index s r) }

open Rust_primitives.Hax

let update_at_tc_array_range_super t l n: t_Index (t_Array t l) (t_Range (int_t n))
  = FStar.Tactics.Typeclasses.solve
let update_at_tc_array_range_to_super t l n: t_Index (t_Array t l) (t_RangeTo (int_t n))
  = FStar.Tactics.Typeclasses.solve
let update_at_tc_array_range_from_super t l n: t_Index (t_Array t l) (t_RangeFrom (int_t n))
  = FStar.Tactics.Typeclasses.solve
let update_at_tc_array_range_full_super t l n: t_Index (t_Array t l) t_RangeFull
  = FStar.Tactics.Typeclasses.solve

val update_at_array_range t l n
  (s: t_Array t l) (i: t_Range (int_t n) {(update_at_tc_array_range_super t l n).in_range s i})
  : (update_at_tc_array_range_super t l n).f_Output -> t_Array t l
val update_at_array_range_to t l n
  (s: t_Array t l) (i: t_RangeTo (int_t n) {(update_at_tc_array_range_to_super t l n).in_range s i})
  : (update_at_tc_array_range_to_super t l n).f_Output -> t_Array t l
val update_at_array_range_from t l n
  (s: t_Array t l) (i: t_RangeFrom (int_t n) {(update_at_tc_array_range_from_super t l n).in_range s i})
  : (update_at_tc_array_range_from_super t l n).f_Output -> t_Array t l
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

instance impl__index_mut_array t l n: t_IndexMut (t_Array t l) (t_Range (int_t n))
  = { out_type = t_Slice t;
      in_range = (fun (s: t_Array t l) (i: t_Range (int_t n)) -> True);
      f_index_mut = (fun s {f_start; f_end} -> 
           if f_end >=. f_start
           then
             ( admit ();
               let len = f_end -! f_start in
               let buffer = B.sub s f_start len in
               {buffer; len})
           else admit()
      );
    }

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

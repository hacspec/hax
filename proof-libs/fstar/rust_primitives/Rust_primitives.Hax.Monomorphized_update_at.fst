module Rust_primitives.Hax.Monomorphized_update_at

open Rust_primitives
open Rust_primitives.Hax
open Core.Ops.Range

let update_at_usize
  (s: t_Slice 't)
  (i: usize {i <. length s}) 
  (x: 't)
  : Pure (t_Array 't (length s))
    (requires (True))
    (ensures (fun res -> res == Seq.upd s (v i) x))
  = update_at s i x

let update_at_range #n
  (s: t_Slice 't)
  (i: t_Range (int_t n) {(impl_index_range_slice 't n).in_range s i}) 
  (x: t_Slice 't)
  : Pure (t_Array 't (length s))
    (requires (Seq.length x == v i.f_end - v i.f_start))
    (ensures (fun res ->
                Seq.slice res 0 (v i.f_start) == Seq.slice s 0 (v i.f_start) /\
                Seq.slice res (v i.f_start) (v i.f_end) == x /\
                Seq.slice res (v i.f_end) (Seq.length res) == Seq.slice s (v i.f_end) (Seq.length s)))
  = let res = update_at s i x in
    admit(); // To be proved
    res
  
let update_at_range_to #n
  (s: t_Slice 't)
  (i: t_RangeTo (int_t n) {(impl_index_range_to_slice 't n).in_range s i}) 
  (x: t_Slice 't)
  : Pure (t_Array 't (length s))
    (requires (Seq.length x == v i.f_end))
    (ensures (fun res ->
                Seq.slice res 0 (v i.f_end) == x /\
                Seq.slice res (v i.f_end) (Seq.length res) == Seq.slice s (v i.f_end) (Seq.length s)))
  = let res = update_at s i x in
    admit();
    res
  
let update_at_range_from #n
  (s: t_Slice 't)
  (i: t_RangeFrom (int_t n) {(impl_index_range_from_slice 't n).in_range s i}) 
  (x: t_Slice 't)
  : Pure (t_Array 't (length s))
    (requires (Seq.length x == Seq.length s - v i.f_start))
    (ensures (fun res ->
                Seq.slice res 0 (v i.f_start) == Seq.slice s 0 (v i.f_start) /\
                Seq.slice res (v i.f_start) (Seq.length res) == x))
  = let res = update_at s i x in
    admit();
    res

let update_at_range_full
  (s: t_Slice 't)
  (i: t_RangeFull {(impl_index_range_full_slice 't).in_range s i}) 
  (x: t_Slice 't)
  : Pure (t_Array 't (length s))
    (requires (Seq.length x == Seq.length s))
    (ensures (fun res -> res == x))
  = let res = update_at s i x in
    admit();
    res



module Rust_primitives.Hax.Monomorphized_update_at

open Rust_primitives
open Rust_primitives.Hax
open Core.Ops.Range

let update_at_usize
  (s: t_Slice 't)
  (i: usize {i <. length s}) 
  (v: 't)
  : t_Array 't (length s)
  = update_at s i v

let update_at_range #n
  (s: t_Slice 't)
  (i: t_Range (int_t n) {(impl_index_range_slice 't n).in_range s i}) 
  (v: t_Slice 't)
  : t_Array 't (length s)
  = update_at s i v
  
let update_at_range_to #n
  (s: t_Slice 't)
  (i: t_RangeTo (int_t n) {(impl_index_range_to_slice 't n).in_range s i}) 
  (v: t_Slice 't)
  : t_Array 't (length s)
  = update_at s i v
  
let update_at_range_from #n
  (s: t_Slice 't)
  (i: t_RangeFrom (int_t n) {(impl_index_range_from_slice 't n).in_range s i}) 
  (v: t_Slice 't)
  : t_Array 't (length s)
  = update_at s i v

let update_at_range_full
  (s: t_Slice 't)
  (i: t_RangeFull {(impl_index_range_full_slice 't).in_range s i}) 
  (v: t_Slice 't)
  : t_Array 't (length s)
  = update_at s i v



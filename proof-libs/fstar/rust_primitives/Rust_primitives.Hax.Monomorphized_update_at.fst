module Rust_primitives.Hax.Monomorphized_update_at

open Rust_primitives
open Rust_primitives.Hax
open Core.Ops.Range
open LowStar.BufferOps
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

// let update_at_usize
//   (s: t_Slice 't)
//   (i: usize {i <. spec_length s}) 
//   (v: 't)
//   : HST.St unit//(t_Array 't (length s))
//   = update_at s i v

inline_for_extraction
let update_array_at_usize
  (s: t_Array 't 'l)
  (i: usize {i <. 'l})
  (v: 't): HST.St unit
  = admit ();
    s.(i) <- v

inline_for_extraction    
let update_slice_at_usize
  (s: t_Slice 't)
  (i: usize {i <. spec_length s}) // {i <. 'l}) 
  (v: 't): HST.St unit
  = admit ();
    (Some?.v s).buffer.(i) <- v

let update_array_at_range #n
  (s: t_Array 't 'n)
  (i: t_Range (int_t n) (* TODO *))
  (v: 't)
  : HST.St unit
  = admit ()

let update_slice_at_range #n
  (s: t_Slice 't)
  (i: t_Range (int_t n) {(impl_index_range_slice 't n).in_range s i}) 
  (v: 't)
  : HST.St unit
  = admit ()
  
let update_slice_at_range_to #n
  (s: t_Slice 't)
  (i: t_RangeTo (int_t n) {(impl_index_range_to_slice 't n).in_range s i}) 
  (v: 't)
  : HST.St unit
  = admit ()
  
let update_array_at_range_to #n
  (s: t_Array 't 'n)
  (i: t_RangeTo (int_t n) (* TODO *)) 
  (v: 't)
  : HST.St unit
  = admit ()
  
let update_slice_at_range_from #n
  (s: t_Slice 't)
  (i: t_RangeFrom (int_t n) {(impl_index_range_from_slice 't n).in_range s i}) 
  (v: 't)
  : HST.St unit
  = admit ()
  
let update_array_at_range_from #n
  (s: t_Array 't 'n)
  (i: t_RangeFrom (int_t n) (* TODO *)) 
  (v: 't)
  : HST.St unit
  = admit ()

let update_slice_at_range_full
  (s: t_Slice 't)
  (i: t_RangeFull {(impl_index_range_full_slice 't).in_range s i}) 
  (v: t_Slice 't)
  : HST.St unit
  = admit ()

let update_array_at_range_full
  (s: t_Array 't 'n)
  (i: t_RangeFull (* TODO *)) 
  (v: 't)
  : HST.St unit
  = admit ()



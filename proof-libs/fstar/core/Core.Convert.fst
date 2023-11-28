module Core.Convert
open Rust_primitives

open LowStar.BufferOps
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

inline_for_extraction
class try_into_tc self t = {
  [@@@FStar.Tactics.Typeclasses.no_method]
  f_Error: Type;
  f_try_into: self -> HST.St (Core.Result.t_Result t f_Error)
}

inline_for_extraction
instance impl_6 (t: Type0) (len: usize): try_into_tc (t_Slice t) (t_Array t len) = {
  f_Error = Core.Array.t_TryFromSliceError;
  f_try_into = (fun (s: t_Slice t) -> 
    if Core.Slice.impl__len s = len
    then Core.Result.Result_Ok (s.buffer)
    else Core.Result.Result_Err Core.Array.TryFromSliceError
  )
}


inline_for_extraction
instance impl_6_refined (t: Type0) (len: usize): try_into_tc (s: t_Slice t {spec_length s == len}) (t_Array t len) = {
  f_Error = Core.Array.t_TryFromSliceError;
  f_try_into = (fun (s: t_Slice t {spec_length s == len}) -> 
    Core.Result.Result_Ok (magic ())//s <: t_Array t len)
  )
}

inline_for_extraction
class t_Into self t = {
  f_into: self -> t;
}

inline_for_extraction
class t_From self t = {
  f_from: t -> self;
}

inline_for_extraction
class t_TryFrom self t = {
  [@@@FStar.Tactics.Typeclasses.no_method]
  f_Error: Type;
  f_try_from: t -> HST.St (Core.Result.t_Result self f_Error);
}


inline_for_extraction
instance integer_into
  (t:inttype) (t':inttype { minint t >= minint t' /\ maxint t <= maxint t' })
  : t_From (int_t t') (int_t t)
  = { f_from = (fun (x: int_t t) -> Rust_primitives.Integers.cast #t #t' x) }

inline_for_extraction
instance into_from_from a b {| t_From a b |}: t_Into b a = {
  f_into = (fun x -> f_from x)
}

inline_for_extraction
instance from_id a: t_From a a = {
  f_from = (fun x -> x)
}

inline_for_extraction
class t_AsRef self t = {
  f_as_ref:  self -> t;
}

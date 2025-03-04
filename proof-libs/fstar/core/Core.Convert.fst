
module Core.Convert
open Rust_primitives

class try_into_tc self t = {
  [@@@FStar.Tactics.Typeclasses.no_method]
  f_Error: Type0;
  f_try_into: self -> Core.Result.t_Result t f_Error
}

instance impl_6 (t: Type0) (len: usize): try_into_tc (t_Slice t) (t_Array t len) = {
  f_Error = Core.Array.t_TryFromSliceError;
  f_try_into = (fun (s: t_Slice t) -> 
    if Core.Slice.impl__len s = len
    then Core.Result.Result_Ok (s <: t_Array t len)
    else Core.Result.Result_Err Core.Array.TryFromSliceError
  )
}

instance impl_6_refined (t: Type0) (len: usize): try_into_tc (s: t_Slice t {Core.Slice.impl__len s == len}) (t_Array t len) = {
  f_Error = Core.Array.t_TryFromSliceError;
  f_try_into = (fun (s: t_Slice t {Core.Slice.impl__len s == len}) -> 
    Core.Result.Result_Ok (s <: t_Array t len)
  )
}

instance integer_try_into (t:inttype) (t':inttype) : try_into_tc (int_t t) (int_t t') = {
  f_Error = Core.Num.Error.t_TryFromIntError;
  f_try_into = (fun (x: int_t t) ->
    if range (v #t x) t'
    then Core.Result.Result_Ok (Rust_primitives.Integers.cast #t #t' x)
    else Core.Result.Result_Err ()
  )
}

class t_Into self t = {
  f_into_pre: self -> bool;
  f_into_post: self -> t -> bool;
  f_into: self -> t;
}

class t_From self t = {
  f_from_pre: t -> bool;
  f_from_post: t -> self -> bool;
  f_from: t -> self;
}

class t_TryFrom self t = {
  [@@@FStar.Tactics.Typeclasses.no_method]
  f_Error: Type0;
  f_try_from_pre: t -> bool;
  f_try_from_post: t -> Core.Result.t_Result self f_Error -> bool;
  f_try_from: t -> Core.Result.t_Result self f_Error;
}

instance integer_into
  (t:inttype) (t':inttype { minint t >= minint t' /\ maxint t <= maxint t' })
  : t_From (int_t t') (int_t t)
  = {
      f_from_pre = (fun _ -> true);
      f_from_post = (fun _ _ -> true);
      f_from = (fun (x: int_t t) -> Rust_primitives.Integers.cast #t #t' x);
    }

instance into_from_from a b {| t_From a b |}: t_Into b a = {
  f_into_pre = (fun _ -> true);
  f_into_post = (fun _ _ -> true);
  f_into = (fun x -> f_from x)
}
instance try_into_from_try_from a b {| i1: t_TryFrom a b |}: try_into_tc b a = {
  f_Error = i1.f_Error;
  f_try_into = (fun x -> f_try_from x)
}

instance from_id a: t_From a a = {
  f_from_pre = (fun _ -> true);
  f_from_post = (fun _ _ -> true);
  f_from = (fun x -> x)
}

class t_AsRef self t = {
  f_as_ref_pre: self -> bool;
  f_as_ref_post: self -> t -> bool;
  f_as_ref: self -> t;
}

instance as_ref_id a: t_AsRef a a = {
  f_as_ref_pre = (fun _ -> true);
  f_as_ref_post = (fun _ _ -> true);
  f_as_ref = (fun x -> x)
}

type t_Infallible = _:unit{False}

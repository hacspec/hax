
module Core.Convert
open Rust_primitives

class try_into_tc self t = {
  [@@@FStar.Tactics.Typeclasses.no_method]
  f_Error: Type;
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

class t_Into self t = {
  f_into: self -> t;
}

class t_From self t = {
  f_from: t -> self;
}

class t_TryFrom self t = {
  [@@@FStar.Tactics.Typeclasses.no_method]
  f_Error: Type;
  f_try_from: t -> Core.Result.t_Result self f_Error;
}

#push-options "--z3rlimit 20"
instance integer_into
  (t:inttype) (t':inttype { Lib.IntTypes.bits   t' > Lib.IntTypes.bits   t 
                          /\ Lib.IntTypes.signed t' = Lib.IntTypes.signed t})
  : t_From (int_t t') (int_t t)
  = { f_from = (fun (x: int_t t) -> 
        assert (minint t >= minint t' /\ maxint t <= maxint t');
        Rust_primitives.Integers.cast #t #t' x
      )
    }
#pop-options

instance into_from_from a b {| t_From a b |}: t_Into b a = {
  f_into = (fun x -> f_from x)
}

instance from_id a: t_From a a = {
  f_from = (fun x -> x)
}

class t_AsRef self t = {
  f_as_ref:  self -> t;
}

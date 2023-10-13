
module Core.Convert
open Rust_primitives

class try_into_tc self t = {
  error: Type;
  try_into: self -> Core.Result.t_Result t error
}

instance try_into_tc_slice t len: try_into_tc (slice t) (array t len) = {
  error = unit;
  try_into = (fun (s: slice t) -> 
    if Core.Slice.impl__len s = len
    then Core.Result.Ok (s <: array t len)
    else Core.Result.Err ()
  )
}

class t_Into self t = {
  f_into: self -> t;
}

class t_From self t = {
  f_from: t -> self;
}

#push-options "--z3rlimit 20"
instance integer_into
  (t:inttype) (t':inttype { Lib.IntTypes.bits   t' > Lib.IntTypes.bits   t 
                          /\ Lib.IntTypes.signed t' = Lib.IntTypes.signed t})
  : t_From (int_t t') (int_t t)
  = { f_from = (fun (x: int_t t) -> 
        assert (minint t >= minint t' /\ maxint t <= maxint t');
        cast #t #t' x
      )
    }
#pop-options

instance into_from_from a b {| t_From a b |}: t_Into b a = {
  f_into = (fun x -> f_from x)
}

instance from_id a: t_From a a = {
  f_from = (fun x -> x)
}


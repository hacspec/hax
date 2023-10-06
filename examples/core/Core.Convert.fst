
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


instance i64_from_i8: t_From i64 i8 = {
  f_from = (fun (x: i8) -> cast x)
}
instance i64_from_i16: t_From i64 i16 = {
  f_from = (fun (x: i16) -> cast x)
}
instance i64_from_i32: t_From i64 i32 = {
  f_from = (fun (x: i32) -> cast x)
}

instance into_from_from a b {| t_From a b |}: t_Into b a = {
  f_into = (fun x -> f_from x)
}

instance from_id a: t_From a a = {
  f_from = (fun x -> x)
}


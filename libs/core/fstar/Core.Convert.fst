module Core.Convert
open Core.Types

class try_into_tc self t = {
  error: Type;
  try_into: self -> Core.Result.t_Result t error
}

instance try_into_tc_slice t len: try_into_tc (slice t) (array t len) = {
  error = unit;
  try_into = (fun (s: slice t) -> 
    if Core.Slice.len_under_impl s = len
    then Core.Result.Ok (s <: array t len)
    else Core.Result.Err ()
  )
}

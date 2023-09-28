module Hax.Lib
open Core.Types
open Core.Array

open FStar.SizeT

type bounded_index (max: usize) = 
  | Bounded: n: usize {v n < v max} -> bounded_index max

instance index_bounded_index_array
  t (len: usize)
  : index (array t len) (bounded_index len)
  = let tc = index_array t len in 
    {
      output = tc.output;
      in_range = (fun (_: array t len) (_: bounded_index len) -> true);
      (.[]) = (fun (s: array t len) (Bounded i) -> s.[i])
    }

instance update_at_bounded_index_array
  t (len: usize)
  : update_at (array t len) (bounded_index len)
  = let super_index = index_bounded_index_array t len in 
    {
      super_index;
      (.[]<-) = (fun (s: array t len) (Bounded i) x -> s.[i] <- x)
    }


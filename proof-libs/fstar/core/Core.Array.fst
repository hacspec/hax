
module Core.Array
open Rust_primitives


open LowStar.BufferOps
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST


inline_for_extraction
type t_TryFromSliceError = | TryFromSliceError

let impl_23__map n (arr: t_Array 'a n) (f: 'a -> 'b): t_Array 'b n  = admit()

inline_for_extraction
let impl_23__as_slice len (arr: t_Array 'a len): HST.St (t_Slice 'a) =
  {buffer = arr; len = len}

inline_for_extraction noextract
let rec from_fn_aux (n: usize) (f: (i:usize{v i < v n}) -> 't) (i: usize {v i <= v n})
: Tot (l: list _ {List.Tot.length l == v n - v i})
      (decreases v n - v i) = 
  if i = n
  then []
  else f i::(from_fn_aux n f (i +. 1ul))

inline_for_extraction noextract
let from_fn (n: usize {v n > 0}) (f: usize -> 't): HST.StackInline (t_Array 't n) (fun _ -> True) (fun _ _ _ -> True)
  = assume (v n < maxint Lib.IntTypes.U32);
    of_list (from_fn_aux n f 0ul)

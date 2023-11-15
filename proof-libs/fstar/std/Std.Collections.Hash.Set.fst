module Std.Collections.Hash.Set

open FStar.FiniteSet.Base

let impl_1__len (s: set t) = cardinality s

let impl__new = empty

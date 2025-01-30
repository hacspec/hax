module Std.Collections.Hash.Map

type t_HashMap ([@@@ strictly_positive] k [@@@ strictly_positive] v [@@@ strictly_positive] s:Type0): eqtype

val impl__new #k #v: unit -> t_HashMap k v Std.Hash.Random.t_RandomState

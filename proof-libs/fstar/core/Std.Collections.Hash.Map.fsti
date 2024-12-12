module Std.Collections.Hash.Map

type t_HashMap (k v s:Type0)

val impl__new #k #v: unit -> t_HashMap k v Std.Hash.Random.t_RandomState

module Core.Slice
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let impl__len
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (self: Core.Primitive.t_Slice v_T)
    : usize =
  Core.Convert.f_from #usize
    #Core.Base.Spec.Haxint.t_HaxInt
    #FStar.Tactics.Typeclasses.solve
    (Core.Base.Seq.len #v_T
        (Core.Clone.f_clone #(Core.Base.Spec.Seq.t_Seq v_T)
            #FStar.Tactics.Typeclasses.solve
            self.Core.Primitive.f_v
          <:
          Core.Base.Spec.Seq.t_Seq v_T)
      <:
      Core.Base.Spec.Haxint.t_HaxInt)

let impl__is_empty
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Clone.t_Clone v_T)
      (self: Core.Primitive.t_Slice v_T)
    : bool = Rust_primitives.Usize.eq (impl__len #v_T self <: usize) (sz 0)

let impl__iter
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Clone.t_Clone v_T)
      (self: Core.Primitive.t_Slice v_T)
    : Core.Slice.Iter.t_Iter v_T = Core.Slice.Iter.impl__new #v_T self

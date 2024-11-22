module Core.Ops.Index_range
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_IndexRange = {
  f_start:usize;
  f_end:usize
}

let impl__IndexRange__len (self: t_IndexRange) : usize =
  Rust_primitives.Usize.sub self.f_end self.f_start

let impl__IndexRange__next_unchecked (self: t_IndexRange) : (t_IndexRange & usize) =
  let value:usize = self.f_start in
  let self:t_IndexRange =
    { self with f_start = Rust_primitives.Usize.add value (sz 1) } <: t_IndexRange
  in
  let hax_temp_output:usize = value in
  self, hax_temp_output <: (t_IndexRange & usize)

let impl__IndexRange__zero_to (v_end: usize) : t_IndexRange =
  { f_start = sz 0; f_end = v_end } <: t_IndexRange

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Iter.Traits.Iterator.t_Iterator t_IndexRange =
  {
    f_Item = usize;
    f_next_pre = (fun (self: t_IndexRange) -> true);
    f_next_post
    =
    (fun (self: t_IndexRange) (out: (t_IndexRange & Core.Option.t_Option usize)) -> true);
    f_next
    =
    (fun (self: t_IndexRange) ->
        let hax_temp_output:Core.Option.t_Option usize =
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_v1 (sz 1)
                    (sz 0)
                    (let list = ["not yet implemented: specification needed"] in
                      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                      Rust_primitives.Hax.array_of_list 1 list)
                    (Core.Fmt.Rt.impl_1__none () <: t_Array Core.Fmt.Rt.t_Argument (sz 0))
                  <:
                  Core.Fmt.t_Arguments)
              <:
              Rust_primitives.Hax.t_Never)
        in
        self, hax_temp_output <: (t_IndexRange & Core.Option.t_Option usize));
    f_size_hint_pre = (fun (self: t_IndexRange) -> true);
    f_size_hint_post
    =
    (fun (self: t_IndexRange) (out: (usize & Core.Option.t_Option usize)) -> true);
    f_size_hint
    =
    (fun (self: t_IndexRange) ->
        let len:usize = impl__IndexRange__len self in
        len, (Core.Option.Option_Some len <: Core.Option.t_Option usize)
        <:
        (usize & Core.Option.t_Option usize));
    f_fold_pre
    =
    (fun
        (#v_B: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Core.Ops.Function.t_FnMut v_F (v_B & (impl_1).f_Item))
        (self: t_IndexRange)
        (init: v_B)
        (f: v_F)
        ->
        true);
    f_fold_post
    =
    (fun
        (#v_B: Type0)
        (#v_F: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Core.Ops.Function.t_FnMut v_F (v_B & (impl_1).f_Item))
        (self: t_IndexRange)
        (init: v_B)
        (f: v_F)
        (out: v_B)
        ->
        true);
    f_fold
    =
    fun
      (#v_B: Type0)
      (#v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
        i3:
        Core.Ops.Function.t_FnMut v_F (v_B & (impl_1).f_Item))
      (self: t_IndexRange)
      (init: v_B)
      (f: v_F)
      ->
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_v1 (sz 1)
                (sz 0)
                (let list = ["not yet implemented: specification needed"] in
                  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                  Rust_primitives.Hax.array_of_list 1 list)
                (Core.Fmt.Rt.impl_1__none () <: t_Array Core.Fmt.Rt.t_Argument (sz 0))
              <:
              Core.Fmt.t_Arguments)
          <:
          Rust_primitives.Hax.t_Never)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Iter.Traits.Exact_size.t_ExactSizeIterator t_IndexRange =
  {
    _super_15444444506782437531 = FStar.Tactics.Typeclasses.solve;
    f_len_pre = (fun (self: t_IndexRange) -> true);
    f_len_post = (fun (self: t_IndexRange) (out: usize) -> true);
    f_len = fun (self: t_IndexRange) -> impl__IndexRange__len self
  }

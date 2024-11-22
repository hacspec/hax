module Core.Iter.Range
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_RangeIteratorImpl (v_Self: Type0) = {
  f_Item:Type0;
  f_spec_next_pre:v_Self -> Type0;
  f_spec_next_post:v_Self -> (v_Self & Core.Option.t_Option f_Item) -> Type0;
  f_spec_next:x0: v_Self
    -> Prims.Pure (v_Self & Core.Option.t_Option f_Item)
        (f_spec_next_pre x0)
        (fun result -> f_spec_next_post x0 result)
}

class t_Step (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9442900250278684536:Core.Clone.t_Clone v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_12866954522599331834:Core.Cmp.t_PartialOrd v_Self
    v_Self;
  f_steps_between_pre:v_Self -> v_Self -> Type0;
  f_steps_between_post:v_Self -> v_Self -> Core.Option.t_Option Core.Primitive.t_usize -> Type0;
  f_steps_between:x0: v_Self -> x1: v_Self
    -> Prims.Pure (Core.Option.t_Option Core.Primitive.t_usize)
        (f_steps_between_pre x0 x1)
        (fun result -> f_steps_between_post x0 x1 result);
  f_forward_checked_pre:v_Self -> Core.Primitive.t_usize -> Type0;
  f_forward_checked_post:v_Self -> Core.Primitive.t_usize -> Core.Option.t_Option v_Self -> Type0;
  f_forward_checked:x0: v_Self -> x1: Core.Primitive.t_usize
    -> Prims.Pure (Core.Option.t_Option v_Self)
        (f_forward_checked_pre x0 x1)
        (fun result -> f_forward_checked_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_A: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Step v_A)
    : t_RangeIteratorImpl (Core.Ops.Range.t_Range v_A) =
  {
    f_Item = v_A;
    f_spec_next_pre = (fun (self: Core.Ops.Range.t_Range v_A) -> true);
    f_spec_next_post
    =
    (fun
        (self: Core.Ops.Range.t_Range v_A)
        (out: (Core.Ops.Range.t_Range v_A & Core.Option.t_Option v_A))
        ->
        true);
    f_spec_next
    =
    fun (self: Core.Ops.Range.t_Range v_A) ->
      let hax_temp_output:Core.Option.t_Option v_A =
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
      self, hax_temp_output <: (Core.Ops.Range.t_Range v_A & Core.Option.t_Option v_A)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_A: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Step v_A)
    : Core.Iter.Traits.Iterator.t_Iterator (Core.Ops.Range.t_Range v_A) =
  {
    f_Item = v_A;
    f_next_pre = (fun (self: Core.Ops.Range.t_Range v_A) -> true);
    f_next_post
    =
    (fun
        (self: Core.Ops.Range.t_Range v_A)
        (out: (Core.Ops.Range.t_Range v_A & Core.Option.t_Option v_A))
        ->
        true);
    f_next
    =
    (fun (self: Core.Ops.Range.t_Range v_A) ->
        let hax_temp_output:Core.Option.t_Option v_A =
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
        self, hax_temp_output <: (Core.Ops.Range.t_Range v_A & Core.Option.t_Option v_A));
    f_size_hint_pre = (fun (self: Core.Ops.Range.t_Range v_A) -> true);
    f_size_hint_post
    =
    (fun (self: Core.Ops.Range.t_Range v_A) (out: (usize & Core.Option.t_Option usize)) -> true);
    f_size_hint
    =
    fun (self: Core.Ops.Range.t_Range v_A) ->
      if self.Core.Ops.Range.f_start <. self.Core.Ops.Range.f_end
      then
        let hint:Core.Option.t_Option Core.Primitive.t_usize =
          f_steps_between #v_A
            #FStar.Tactics.Typeclasses.solve
            self.Core.Ops.Range.f_start
            self.Core.Ops.Range.f_end
        in
        sz 0, (Core.Option.Option_Some (sz 0) <: Core.Option.t_Option usize)
        <:
        (usize & Core.Option.t_Option usize)
      else
        sz 0, (Core.Option.Option_Some (sz 0) <: Core.Option.t_Option usize)
        <:
        (usize & Core.Option.t_Option usize)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: t_Step Core.Primitive.t_u8 =
  {
    _super_9442900250278684536 = FStar.Tactics.Typeclasses.solve;
    _super_12866954522599331834 = FStar.Tactics.Typeclasses.solve;
    f_steps_between_pre = (fun (start: Core.Primitive.t_u8) (v_end: Core.Primitive.t_u8) -> true);
    f_steps_between_post
    =
    (fun
        (start: Core.Primitive.t_u8)
        (v_end: Core.Primitive.t_u8)
        (out: Core.Option.t_Option Core.Primitive.t_usize)
        ->
        true);
    f_steps_between
    =
    (fun (start: Core.Primitive.t_u8) (v_end: Core.Primitive.t_u8) ->
        if start <=. v_end
        then
          Core.Option.Option_Some
          (Core.Convert.f_into #Core.Primitive.t_u8
              #Core.Primitive.t_usize
              #FStar.Tactics.Typeclasses.solve
              ((Core.Clone.f_clone #Core.Primitive.t_u8 #FStar.Tactics.Typeclasses.solve v_end
                  <:
                  Core.Primitive.t_u8) -!
                (Core.Clone.f_clone #Core.Primitive.t_u8 #FStar.Tactics.Typeclasses.solve start
                  <:
                  Core.Primitive.t_u8)
                <:
                Core.Primitive.t_u8))
          <:
          Core.Option.t_Option Core.Primitive.t_usize
        else Core.Option.Option_None <: Core.Option.t_Option Core.Primitive.t_usize);
    f_forward_checked_pre = (fun (start: Core.Primitive.t_u8) (n: Core.Primitive.t_usize) -> true);
    f_forward_checked_post
    =
    (fun
        (start: Core.Primitive.t_u8)
        (n: Core.Primitive.t_usize)
        (out: Core.Option.t_Option Core.Primitive.t_u8)
        ->
        true);
    f_forward_checked
    =
    fun (start: Core.Primitive.t_u8) (n: Core.Primitive.t_usize) ->
      match
        Core.Convert.f_try_from #Core.Primitive.t_u8
          #Core.Primitive.t_usize
          #FStar.Tactics.Typeclasses.solve
          n
      with
      | Core.Result.Result_Ok n -> Core.Num.impl_6__checked_add start n
      | Core.Result.Result_Err _ ->
        Core.Option.Option_None <: Core.Option.t_Option Core.Primitive.t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: t_Step Core.Primitive.t_u16 =
  {
    _super_9442900250278684536 = FStar.Tactics.Typeclasses.solve;
    _super_12866954522599331834 = FStar.Tactics.Typeclasses.solve;
    f_steps_between_pre = (fun (start: Core.Primitive.t_u16) (v_end: Core.Primitive.t_u16) -> true);
    f_steps_between_post
    =
    (fun
        (start: Core.Primitive.t_u16)
        (v_end: Core.Primitive.t_u16)
        (out: Core.Option.t_Option Core.Primitive.t_usize)
        ->
        true);
    f_steps_between
    =
    (fun (start: Core.Primitive.t_u16) (v_end: Core.Primitive.t_u16) ->
        if start <=. v_end
        then
          Core.Option.Option_Some
          (Core.Convert.f_into #Core.Primitive.t_u16
              #Core.Primitive.t_usize
              #FStar.Tactics.Typeclasses.solve
              ((Core.Clone.f_clone #Core.Primitive.t_u16 #FStar.Tactics.Typeclasses.solve v_end
                  <:
                  Core.Primitive.t_u16) -!
                (Core.Clone.f_clone #Core.Primitive.t_u16 #FStar.Tactics.Typeclasses.solve start
                  <:
                  Core.Primitive.t_u16)
                <:
                Core.Primitive.t_u16))
          <:
          Core.Option.t_Option Core.Primitive.t_usize
        else Core.Option.Option_None <: Core.Option.t_Option Core.Primitive.t_usize);
    f_forward_checked_pre = (fun (start: Core.Primitive.t_u16) (n: Core.Primitive.t_usize) -> true);
    f_forward_checked_post
    =
    (fun
        (start: Core.Primitive.t_u16)
        (n: Core.Primitive.t_usize)
        (out: Core.Option.t_Option Core.Primitive.t_u16)
        ->
        true);
    f_forward_checked
    =
    fun (start: Core.Primitive.t_u16) (n: Core.Primitive.t_usize) ->
      match
        Core.Convert.f_try_from #Core.Primitive.t_u16
          #Core.Primitive.t_usize
          #FStar.Tactics.Typeclasses.solve
          n
      with
      | Core.Result.Result_Ok n -> Core.Num.impl_7__checked_add start n
      | Core.Result.Result_Err _ ->
        Core.Option.Option_None <: Core.Option.t_Option Core.Primitive.t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: t_Step Core.Primitive.t_u32 =
  {
    _super_9442900250278684536 = FStar.Tactics.Typeclasses.solve;
    _super_12866954522599331834 = FStar.Tactics.Typeclasses.solve;
    f_steps_between_pre = (fun (start: Core.Primitive.t_u32) (v_end: Core.Primitive.t_u32) -> true);
    f_steps_between_post
    =
    (fun
        (start: Core.Primitive.t_u32)
        (v_end: Core.Primitive.t_u32)
        (out: Core.Option.t_Option Core.Primitive.t_usize)
        ->
        true);
    f_steps_between
    =
    (fun (start: Core.Primitive.t_u32) (v_end: Core.Primitive.t_u32) ->
        if start <=. v_end
        then
          Core.Option.Option_Some
          (Core.Convert.f_into #Core.Primitive.t_u32
              #Core.Primitive.t_usize
              #FStar.Tactics.Typeclasses.solve
              ((Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve v_end
                  <:
                  Core.Primitive.t_u32) -!
                (Core.Clone.f_clone #Core.Primitive.t_u32 #FStar.Tactics.Typeclasses.solve start
                  <:
                  Core.Primitive.t_u32)
                <:
                Core.Primitive.t_u32))
          <:
          Core.Option.t_Option Core.Primitive.t_usize
        else Core.Option.Option_None <: Core.Option.t_Option Core.Primitive.t_usize);
    f_forward_checked_pre = (fun (start: Core.Primitive.t_u32) (n: Core.Primitive.t_usize) -> true);
    f_forward_checked_post
    =
    (fun
        (start: Core.Primitive.t_u32)
        (n: Core.Primitive.t_usize)
        (out: Core.Option.t_Option Core.Primitive.t_u32)
        ->
        true);
    f_forward_checked
    =
    fun (start: Core.Primitive.t_u32) (n: Core.Primitive.t_usize) ->
      match
        Core.Convert.f_try_from #Core.Primitive.t_u32
          #Core.Primitive.t_usize
          #FStar.Tactics.Typeclasses.solve
          n
      with
      | Core.Result.Result_Ok n -> Core.Num.impl_8__checked_add start n
      | Core.Result.Result_Err _ ->
        Core.Option.Option_None <: Core.Option.t_Option Core.Primitive.t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: t_Step Core.Primitive.t_u64 =
  {
    _super_9442900250278684536 = FStar.Tactics.Typeclasses.solve;
    _super_12866954522599331834 = FStar.Tactics.Typeclasses.solve;
    f_steps_between_pre = (fun (start: Core.Primitive.t_u64) (v_end: Core.Primitive.t_u64) -> true);
    f_steps_between_post
    =
    (fun
        (start: Core.Primitive.t_u64)
        (v_end: Core.Primitive.t_u64)
        (out: Core.Option.t_Option Core.Primitive.t_usize)
        ->
        true);
    f_steps_between
    =
    (fun (start: Core.Primitive.t_u64) (v_end: Core.Primitive.t_u64) ->
        if start <=. v_end
        then
          Core.Option.Option_Some
          (Core.Convert.f_into #Core.Primitive.t_u64
              #Core.Primitive.t_usize
              #FStar.Tactics.Typeclasses.solve
              ((Core.Clone.f_clone #Core.Primitive.t_u64 #FStar.Tactics.Typeclasses.solve v_end
                  <:
                  Core.Primitive.t_u64) -!
                (Core.Clone.f_clone #Core.Primitive.t_u64 #FStar.Tactics.Typeclasses.solve start
                  <:
                  Core.Primitive.t_u64)
                <:
                Core.Primitive.t_u64))
          <:
          Core.Option.t_Option Core.Primitive.t_usize
        else Core.Option.Option_None <: Core.Option.t_Option Core.Primitive.t_usize);
    f_forward_checked_pre = (fun (start: Core.Primitive.t_u64) (n: Core.Primitive.t_usize) -> true);
    f_forward_checked_post
    =
    (fun
        (start: Core.Primitive.t_u64)
        (n: Core.Primitive.t_usize)
        (out: Core.Option.t_Option Core.Primitive.t_u64)
        ->
        true);
    f_forward_checked
    =
    fun (start: Core.Primitive.t_u64) (n: Core.Primitive.t_usize) ->
      match
        Core.Convert.f_try_from #Core.Primitive.t_u64
          #Core.Primitive.t_usize
          #FStar.Tactics.Typeclasses.solve
          n
      with
      | Core.Result.Result_Ok n -> Core.Num.impl_9__checked_add start n
      | Core.Result.Result_Err _ ->
        Core.Option.Option_None <: Core.Option.t_Option Core.Primitive.t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: t_Step Core.Primitive.t_u128 =
  {
    _super_9442900250278684536 = FStar.Tactics.Typeclasses.solve;
    _super_12866954522599331834 = FStar.Tactics.Typeclasses.solve;
    f_steps_between_pre
    =
    (fun (start: Core.Primitive.t_u128) (v_end: Core.Primitive.t_u128) -> true);
    f_steps_between_post
    =
    (fun
        (start: Core.Primitive.t_u128)
        (v_end: Core.Primitive.t_u128)
        (out: Core.Option.t_Option Core.Primitive.t_usize)
        ->
        true);
    f_steps_between
    =
    (fun (start: Core.Primitive.t_u128) (v_end: Core.Primitive.t_u128) ->
        if start <=. v_end
        then
          Core.Result.impl__ok #Core.Primitive.t_usize
            #Core.Convert.t_Infallible
            (Core.Convert.f_try_from #Core.Primitive.t_usize
                #Core.Primitive.t_u128
                #FStar.Tactics.Typeclasses.solve
                ((Core.Clone.f_clone #Core.Primitive.t_u128 #FStar.Tactics.Typeclasses.solve v_end
                    <:
                    Core.Primitive.t_u128) -!
                  (Core.Clone.f_clone #Core.Primitive.t_u128 #FStar.Tactics.Typeclasses.solve start
                    <:
                    Core.Primitive.t_u128)
                  <:
                  Core.Primitive.t_u128)
              <:
              Core.Result.t_Result Core.Primitive.t_usize Core.Convert.t_Infallible)
        else Core.Option.Option_None <: Core.Option.t_Option Core.Primitive.t_usize);
    f_forward_checked_pre = (fun (start: Core.Primitive.t_u128) (n: Core.Primitive.t_usize) -> true);
    f_forward_checked_post
    =
    (fun
        (start: Core.Primitive.t_u128)
        (n: Core.Primitive.t_usize)
        (out: Core.Option.t_Option Core.Primitive.t_u128)
        ->
        true);
    f_forward_checked
    =
    fun (start: Core.Primitive.t_u128) (n: Core.Primitive.t_usize) ->
      Core.Option.Option_None <: Core.Option.t_Option Core.Primitive.t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: t_Step Core.Primitive.t_usize =
  {
    _super_9442900250278684536 = FStar.Tactics.Typeclasses.solve;
    _super_12866954522599331834 = FStar.Tactics.Typeclasses.solve;
    f_steps_between_pre
    =
    (fun (start: Core.Primitive.t_usize) (v_end: Core.Primitive.t_usize) -> true);
    f_steps_between_post
    =
    (fun
        (start: Core.Primitive.t_usize)
        (v_end: Core.Primitive.t_usize)
        (out: Core.Option.t_Option Core.Primitive.t_usize)
        ->
        true);
    f_steps_between
    =
    (fun (start: Core.Primitive.t_usize) (v_end: Core.Primitive.t_usize) ->
        if start <=. v_end
        then
          Core.Option.Option_Some
          (Core.Convert.f_into #Core.Primitive.t_usize
              #Core.Primitive.t_usize
              #FStar.Tactics.Typeclasses.solve
              ((Core.Clone.f_clone #Core.Primitive.t_usize #FStar.Tactics.Typeclasses.solve v_end
                  <:
                  Core.Primitive.t_usize) -!
                (Core.Clone.f_clone #Core.Primitive.t_usize #FStar.Tactics.Typeclasses.solve start
                  <:
                  Core.Primitive.t_usize)
                <:
                Core.Primitive.t_usize))
          <:
          Core.Option.t_Option Core.Primitive.t_usize
        else Core.Option.Option_None <: Core.Option.t_Option Core.Primitive.t_usize);
    f_forward_checked_pre
    =
    (fun (start: Core.Primitive.t_usize) (n: Core.Primitive.t_usize) -> true);
    f_forward_checked_post
    =
    (fun
        (start: Core.Primitive.t_usize)
        (n: Core.Primitive.t_usize)
        (out: Core.Option.t_Option Core.Primitive.t_usize)
        ->
        true);
    f_forward_checked
    =
    fun (start: Core.Primitive.t_usize) (n: Core.Primitive.t_usize) ->
      match
        Core.Convert.f_try_from #Core.Primitive.t_usize
          #Core.Primitive.t_usize
          #FStar.Tactics.Typeclasses.solve
          n
      with
      | Core.Result.Result_Ok n -> Core.Num.impl_11__checked_add start n
      | Core.Result.Result_Err _ ->
        Core.Option.Option_None <: Core.Option.t_Option Core.Primitive.t_usize
  }

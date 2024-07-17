module Hax_secret_integers.Public_integers
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Hax_secret_integers.Traits.t_EncodeOps u32 u8 (sz 4) =
  {
    f_to_le_bytes_pre = (fun (self: u32) -> true);
    f_to_le_bytes_post = (fun (self: u32) (out: t_Array u8 (sz 4)) -> true);
    f_to_le_bytes = (fun (self: u32) -> Core.Num.impl__u32__to_le_bytes self);
    f_to_be_bytes_pre = (fun (self: u32) -> true);
    f_to_be_bytes_post = (fun (self: u32) (out: t_Array u8 (sz 4)) -> true);
    f_to_be_bytes = (fun (self: u32) -> Core.Num.impl__u32__to_be_bytes self);
    f_from_le_bytes_pre = (fun (x: t_Array u8 (sz 4)) -> true);
    f_from_le_bytes_post = (fun (x: t_Array u8 (sz 4)) (out: u32) -> true);
    f_from_le_bytes = (fun (x: t_Array u8 (sz 4)) -> Core.Num.impl__u32__from_le_bytes x);
    f_from_be_bytes_pre = (fun (x: t_Array u8 (sz 4)) -> true);
    f_from_be_bytes_post = (fun (x: t_Array u8 (sz 4)) (out: u32) -> true);
    f_from_be_bytes = fun (x: t_Array u8 (sz 4)) -> Core.Num.impl__u32__from_be_bytes x
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6 (v_N: usize) : Hax_secret_integers.Traits.t_TryDecodeOps (t_Array u32 v_N) u8 =
  {
    f_try_from_le_bytes_pre = (fun (x: t_Slice u8) -> v_N <. (sz 65536 /! sz 4 <: usize));
    f_try_from_le_bytes_post
    =
    (fun (x: t_Slice u8) (out: Core.Result.t_Result (t_Array u32 v_N) Prims.unit) ->
        v_N <. (sz 65536 /! sz 4 <: usize) &&
        (if (Core.Slice.impl__len #u8 x <: usize) =. (v_N *! sz 4 <: usize)
          then Core.Result.impl__is_ok #(t_Array u32 v_N) #Prims.unit out
          else Core.Result.impl__is_err #(t_Array u32 v_N) #Prims.unit out));
    f_try_from_le_bytes
    =
    (fun (x: t_Slice u8) -> Hax_secret_integers.Traits.try_from_le_bytes #u8 (sz 4) #u32 v_N x);
    f_try_from_be_bytes_pre = (fun (x: t_Slice u8) -> v_N <. (sz 65536 /! sz 4 <: usize));
    f_try_from_be_bytes_post
    =
    (fun (x: t_Slice u8) (out: Core.Result.t_Result (t_Array u32 v_N) Prims.unit) ->
        v_N <. (sz 65536 /! sz 4 <: usize) &&
        (if (Core.Slice.impl__len #u8 x <: usize) =. (v_N *! sz 4 <: usize)
          then Core.Result.impl__is_ok #(t_Array u32 v_N) #Prims.unit out
          else Core.Result.impl__is_err #(t_Array u32 v_N) #Prims.unit out));
    f_try_from_be_bytes
    =
    fun (x: t_Slice u8) -> Hax_secret_integers.Traits.try_from_be_bytes #u8 (sz 4) #u32 v_N x
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5 (v_N v_B: usize) : Hax_secret_integers.Traits.t_TryEncodeOps (t_Array u32 v_N) u8 v_B =
  {
    f_try_to_le_bytes_pre = (fun (self: t_Array u32 v_N) -> v_N <. (sz 65536 /! sz 4 <: usize));
    f_try_to_le_bytes_post
    =
    (fun (self: t_Array u32 v_N) (out: Core.Result.t_Result (t_Array u8 v_B) Prims.unit) ->
        v_N <. (sz 65536 /! sz 4 <: usize) &&
        (if v_B =. (v_N *! sz 4 <: usize)
          then Core.Result.impl__is_ok #(t_Array u8 v_B) #Prims.unit out
          else Core.Result.impl__is_err #(t_Array u8 v_B) #Prims.unit out));
    f_try_to_le_bytes
    =
    (fun (self: t_Array u32 v_N) ->
        Hax_secret_integers.Traits.try_to_le_bytes #u8 (sz 4) #u32 v_N v_B self);
    f_try_to_be_bytes_pre = (fun (self: t_Array u32 v_N) -> v_N <. (sz 65536 /! sz 4 <: usize));
    f_try_to_be_bytes_post
    =
    (fun (self: t_Array u32 v_N) (out: Core.Result.t_Result (t_Array u8 v_B) Prims.unit) ->
        v_N <. (sz 65536 /! sz 4 <: usize) &&
        (if v_B =. (v_N *! sz 4 <: usize)
          then Core.Result.impl__is_ok #(t_Array u8 v_B) #Prims.unit out
          else Core.Result.impl__is_err #(t_Array u8 v_B) #Prims.unit out));
    f_try_to_be_bytes
    =
    fun (self: t_Array u32 v_N) ->
      Hax_secret_integers.Traits.try_to_be_bytes #u8 (sz 4) #u32 v_N v_B self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) : Hax_secret_integers.Traits.t_Classify v_T =
  {
    f_ClassifiedOutput = v_T;
    f_classify_pre = (fun (self: v_T) -> true);
    f_classify_post = (fun (self: v_T) (out: v_T) -> true);
    f_classify = fun (self: v_T) -> self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_T: Type0) : Hax_secret_integers.Traits.t_Declassify v_T =
  {
    f_DeclassifiedOutput = v_T;
    f_declassify_pre = (fun (self: v_T) -> true);
    f_declassify_post = (fun (self: v_T) (out: v_T) -> true);
    f_declassify = fun (self: v_T) -> self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_T: Type0) : Hax_secret_integers.Traits.t_ClassifyEach v_T =
  {
    f_ClassifiedEachOutput = v_T;
    f_classify_each_pre = (fun (self: v_T) -> true);
    f_classify_each_post = (fun (self: v_T) (out: v_T) -> true);
    f_classify_each = fun (self: v_T) -> self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3 (#v_T: Type0) : Hax_secret_integers.Traits.t_DeclassifyEach v_T =
  {
    f_DeclassifiedEachOutput = v_T;
    f_declassify_each_pre = (fun (self: v_T) -> true);
    f_declassify_each_post = (fun (self: v_T) (out: v_T) -> true);
    f_declassify_each = fun (self: v_T) -> self
  }

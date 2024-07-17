module Hax_secret_integers.Traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_Classify (v_Self: Type0) = {
  f_ClassifiedOutput:Type0;
  f_classify_pre:v_Self -> bool;
  f_classify_post:v_Self -> f_ClassifiedOutput -> bool;
  f_classify:x0: v_Self
    -> Prims.Pure f_ClassifiedOutput (f_classify_pre x0) (fun result -> f_classify_post x0 result)
}

class t_ClassifyEach (v_Self: Type0) = {
  f_ClassifiedEachOutput:Type0;
  f_classify_each_pre:v_Self -> bool;
  f_classify_each_post:v_Self -> f_ClassifiedEachOutput -> bool;
  f_classify_each:x0: v_Self
    -> Prims.Pure f_ClassifiedEachOutput
        (f_classify_each_pre x0)
        (fun result -> f_classify_each_post x0 result)
}

class t_Declassify (v_Self: Type0) = {
  f_DeclassifiedOutput:Type0;
  f_declassify_pre:v_Self -> bool;
  f_declassify_post:v_Self -> f_DeclassifiedOutput -> bool;
  f_declassify:x0: v_Self
    -> Prims.Pure f_DeclassifiedOutput
        (f_declassify_pre x0)
        (fun result -> f_declassify_post x0 result)
}

class t_DeclassifyEach (v_Self: Type0) = {
  f_DeclassifiedEachOutput:Type0;
  f_declassify_each_pre:v_Self -> bool;
  f_declassify_each_post:v_Self -> f_DeclassifiedEachOutput -> bool;
  f_declassify_each:x0: v_Self
    -> Prims.Pure f_DeclassifiedEachOutput
        (f_declassify_each_pre x0)
        (fun result -> f_declassify_each_post x0 result)
}

class t_EncodeOps (v_Self: Type0) (v_T: Type0) (v_N: usize) = {
  f_to_le_bytes_pre:v_Self -> bool;
  f_to_le_bytes_post:v_Self -> t_Array v_T v_N -> bool;
  f_to_le_bytes:x0: v_Self
    -> Prims.Pure (t_Array v_T v_N)
        (f_to_le_bytes_pre x0)
        (fun result -> f_to_le_bytes_post x0 result);
  f_to_be_bytes_pre:v_Self -> bool;
  f_to_be_bytes_post:v_Self -> t_Array v_T v_N -> bool;
  f_to_be_bytes:x0: v_Self
    -> Prims.Pure (t_Array v_T v_N)
        (f_to_be_bytes_pre x0)
        (fun result -> f_to_be_bytes_post x0 result);
  f_from_le_bytes_pre:t_Array v_T v_N -> bool;
  f_from_le_bytes_post:t_Array v_T v_N -> v_Self -> bool;
  f_from_le_bytes:x0: t_Array v_T v_N
    -> Prims.Pure v_Self (f_from_le_bytes_pre x0) (fun result -> f_from_le_bytes_post x0 result);
  f_from_be_bytes_pre:t_Array v_T v_N -> bool;
  f_from_be_bytes_post:t_Array v_T v_N -> v_Self -> bool;
  f_from_be_bytes:x0: t_Array v_T v_N
    -> Prims.Pure v_Self (f_from_be_bytes_pre x0) (fun result -> f_from_be_bytes_post x0 result)
}

class t_IntOps (v_Self: Type0) = {
  f_wrapping_add_pre:#v_T: Type0 -> {| i1: Core.Convert.t_Into v_T v_Self |} -> v_Self -> v_T
    -> bool;
  f_wrapping_add_post:
      #v_T: Type0 ->
      {| i1: Core.Convert.t_Into v_T v_Self |} ->
      v_Self ->
      v_T ->
      v_Self
    -> bool;
  f_wrapping_add:#v_T: Type0 -> {| i1: Core.Convert.t_Into v_T v_Self |} -> x0: v_Self -> x1: v_T
    -> Prims.Pure v_Self
        (f_wrapping_add_pre #v_T #i1 x0 x1)
        (fun result -> f_wrapping_add_post #v_T #i1 x0 x1 result);
  f_wrapping_sub_pre:#v_T: Type0 -> {| i2: Core.Convert.t_Into v_T v_Self |} -> v_Self -> v_T
    -> bool;
  f_wrapping_sub_post:
      #v_T: Type0 ->
      {| i2: Core.Convert.t_Into v_T v_Self |} ->
      v_Self ->
      v_T ->
      v_Self
    -> bool;
  f_wrapping_sub:#v_T: Type0 -> {| i2: Core.Convert.t_Into v_T v_Self |} -> x0: v_Self -> x1: v_T
    -> Prims.Pure v_Self
        (f_wrapping_sub_pre #v_T #i2 x0 x1)
        (fun result -> f_wrapping_sub_post #v_T #i2 x0 x1 result);
  f_wrapping_mul_pre:#v_T: Type0 -> {| i2: Core.Convert.t_Into v_T v_Self |} -> v_Self -> v_T
    -> bool;
  f_wrapping_mul_post:
      #v_T: Type0 ->
      {| i2: Core.Convert.t_Into v_T v_Self |} ->
      v_Self ->
      v_T ->
      v_Self
    -> bool;
  f_wrapping_mul:#v_T: Type0 -> {| i2: Core.Convert.t_Into v_T v_Self |} -> x0: v_Self -> x1: v_T
    -> Prims.Pure v_Self
        (f_wrapping_mul_pre #v_T #i2 x0 x1)
        (fun result -> f_wrapping_mul_post #v_T #i2 x0 x1 result);
  f_rotate_left_pre:v_Self -> u32 -> bool;
  f_rotate_left_post:v_Self -> u32 -> v_Self -> bool;
  f_rotate_left:x0: v_Self -> x1: u32
    -> Prims.Pure v_Self (f_rotate_left_pre x0 x1) (fun result -> f_rotate_left_post x0 x1 result);
  f_rotate_right_pre:v_Self -> u32 -> bool;
  f_rotate_right_post:v_Self -> u32 -> v_Self -> bool;
  f_rotate_right:x0: v_Self -> x1: u32
    -> Prims.Pure v_Self (f_rotate_right_pre x0 x1) (fun result -> f_rotate_right_post x0 x1 result)
}

class t_TryDecodeOps (v_Self: Type0) (v_T: Type0) = {
  f_try_from_le_bytes_pre:t_Slice v_T -> bool;
  f_try_from_le_bytes_post:t_Slice v_T -> Core.Result.t_Result v_Self Prims.unit -> bool;
  f_try_from_le_bytes:x0: t_Slice v_T
    -> Prims.Pure (Core.Result.t_Result v_Self Prims.unit)
        (f_try_from_le_bytes_pre x0)
        (fun result -> f_try_from_le_bytes_post x0 result);
  f_try_from_be_bytes_pre:t_Slice v_T -> bool;
  f_try_from_be_bytes_post:t_Slice v_T -> Core.Result.t_Result v_Self Prims.unit -> bool;
  f_try_from_be_bytes:x0: t_Slice v_T
    -> Prims.Pure (Core.Result.t_Result v_Self Prims.unit)
        (f_try_from_be_bytes_pre x0)
        (fun result -> f_try_from_be_bytes_post x0 result)
}

class t_TryEncodeOps (v_Self: Type0) (v_T: Type0) (v_N: usize) = {
  f_try_to_le_bytes_pre:v_Self -> bool;
  f_try_to_le_bytes_post:v_Self -> Core.Result.t_Result (t_Array v_T v_N) Prims.unit -> bool;
  f_try_to_le_bytes:x0: v_Self
    -> Prims.Pure (Core.Result.t_Result (t_Array v_T v_N) Prims.unit)
        (f_try_to_le_bytes_pre x0)
        (fun result -> f_try_to_le_bytes_post x0 result);
  f_try_to_be_bytes_pre:v_Self -> bool;
  f_try_to_be_bytes_post:v_Self -> Core.Result.t_Result (t_Array v_T v_N) Prims.unit -> bool;
  f_try_to_be_bytes:x0: v_Self
    -> Prims.Pure (Core.Result.t_Result (t_Array v_T v_N) Prims.unit)
        (f_try_to_be_bytes_pre x0)
        (fun result -> f_try_to_be_bytes_post x0 result)
}

val try_from_be_bytes
      (#v_U: Type0)
      (v_C: usize)
      (#v_T: Type0)
      (v_N: usize)
      {| i2: t_EncodeOps v_T v_U v_C |}
      (x: t_Slice v_U)
    : Prims.Pure (Core.Result.t_Result (t_Array v_T v_N) Prims.unit)
      (requires v_C >. sz 0 && v_C <=. sz 16 && v_N <=. (sz 65536 /! v_C <: usize))
      (ensures
        fun result ->
          let result:Core.Result.t_Result (t_Array v_T v_N) Prims.unit = result in
          if (Core.Slice.impl__len #v_U x <: usize) =. (v_N *! v_C <: usize)
          then Core.Result.impl__is_ok #(t_Array v_T v_N) #Prims.unit result
          else Core.Result.impl__is_err #(t_Array v_T v_N) #Prims.unit result)

val try_from_le_bytes
      (#v_U: Type0)
      (v_C: usize)
      (#v_T: Type0)
      (v_N: usize)
      {| i2: t_EncodeOps v_T v_U v_C |}
      (x: t_Slice v_U)
    : Prims.Pure (Core.Result.t_Result (t_Array v_T v_N) Prims.unit)
      (requires v_C >. sz 0 && v_C <=. sz 16 && v_N <=. (sz 65536 /! v_C <: usize))
      (ensures
        fun result ->
          let result:Core.Result.t_Result (t_Array v_T v_N) Prims.unit = result in
          if (Core.Slice.impl__len #v_U x <: usize) =. (v_N *! v_C <: usize)
          then Core.Result.impl__is_ok #(t_Array v_T v_N) #Prims.unit result
          else Core.Result.impl__is_err #(t_Array v_T v_N) #Prims.unit result)

val try_to_be_bytes
      (#v_U: Type0)
      (v_C: usize)
      (#v_T: Type0)
      (v_N v_B: usize)
      {| i2: Core.Clone.t_Clone v_U |}
      {| i3: t_EncodeOps v_T v_U v_C |}
      (x: t_Array v_T v_N)
    : Prims.Pure (Core.Result.t_Result (t_Array v_U v_B) Prims.unit)
      (requires v_C >. sz 0 && v_C <=. sz 16 && v_N <=. (sz 65536 /! v_C <: usize))
      (ensures
        fun result ->
          let result:Core.Result.t_Result (t_Array v_U v_B) Prims.unit = result in
          if v_B =. (v_N *! v_C <: usize)
          then Core.Result.impl__is_ok #(t_Array v_U v_B) #Prims.unit result
          else Core.Result.impl__is_err #(t_Array v_U v_B) #Prims.unit result)

val try_to_le_bytes
      (#v_U: Type0)
      (v_C: usize)
      (#v_T: Type0)
      (v_N v_B: usize)
      {| i2: Core.Clone.t_Clone v_U |}
      {| i3: t_EncodeOps v_T v_U v_C |}
      (x: t_Array v_T v_N)
    : Prims.Pure (Core.Result.t_Result (t_Array v_U v_B) Prims.unit)
      (requires v_C >. sz 0 && v_C <=. sz 16 && v_N <=. (sz 65536 /! v_C <: usize))
      (ensures
        fun result ->
          let result:Core.Result.t_Result (t_Array v_U v_B) Prims.unit = result in
          if v_B =. (v_N *! v_C <: usize)
          then Core.Result.impl__is_ok #(t_Array v_U v_B) #Prims.unit result
          else Core.Result.impl__is_err #(t_Array v_U v_B) #Prims.unit result)

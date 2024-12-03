(* File automatically generated by Hacspec *)
From Coq Require Import ZArith.
Require Import List.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Require Import Ascii.
Require Import String.
Require Import Coq.Floats.Floats.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(* From Core Require Import Core. *)

From Core Require Import Core_Base_Spec.
Export Core_Base_Spec.

From Core Require Import Core_Base.
Export Core_Base.

From Core Require Import Core (t_primitive).
Export Core (t_primitive).

From Core Require Import Core (t_cmp).
Export Core (t_cmp).

From Core Require Import Core (t_convert).
Export Core (t_convert).

(* NotImplementedYet *)

Notation "'impl_24__from_u128_binary'" := (from_u128_binary).

Notation "'impl_8'" := (impl_8).

Notation "'impl_20'" := (impl_20).

Notation "'impl_24__from_u16_binary'" := (from_u16_binary).

Notation "'impl_2'" := (impl_2).

Notation "'impl_14'" := (impl_14).

Notation "'impl_24__from_u32_binary'" := (from_u32_binary).

Notation "'impl_4'" := (impl_4).

Notation "'impl_16'" := (impl_16).

Notation "'impl_24__from_u64_binary'" := (from_u64_binary).

Notation "'impl_6'" := (impl_6).

Notation "'impl_18'" := (impl_18).

Notation "'impl_24__from_u8_binary'" := (from_u8_binary).

Notation "'impl'" := (impl).

Notation "'impl_12'" := (impl_12).

Notation "'impl_24__from_usize_binary'" := (from_usize_binary).

Notation "'impl_10'" := (impl_10).

Notation "'impl_22'" := (impl_22).

Notation "'impl_24__to_u128_binary'" := (to_u128_binary).

Notation "'impl_9'" := (impl_9).

Notation "'impl_21'" := (impl_21).

Notation "'impl_24__to_u16_binary'" := (to_u16_binary).

Notation "'impl_3'" := (impl_3).

Notation "'impl_15'" := (impl_15).

Notation "'impl_24__to_u32_binary'" := (to_u32_binary).

Notation "'impl_5'" := (impl_5).

Notation "'impl_17'" := (impl_17).

Notation "'impl_24__to_u64_binary'" := (to_u64_binary).

Notation "'impl_7'" := (impl_7).

Notation "'impl_19'" := (impl_19).

Notation "'impl_24__to_u8_binary'" := (to_u8_binary).

Notation "'impl_1'" := (impl_1).

Notation "'impl_13'" := (impl_13).

Notation "'impl_24__to_usize_binary'" := (to_usize_binary).

Notation "'impl_11'" := (impl_11).

Notation "'impl_23'" := (impl_23).
module Core.Base.Spec.Constants
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_BITS_128_: Core.Base.Spec.Haxint.t_HaxInt =
  {
    Core.Base.Spec.Haxint.f_v
    =
    Alloc.Borrow.Cow_Borrowed
    ((let list = [128uy] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list)
      <:
      t_Slice u8)
    <:
    Alloc.Borrow.t_Cow (t_Slice u8)
  }
  <:
  Core.Base.Spec.Haxint.t_HaxInt

let v_BITS_16_: Core.Base.Spec.Haxint.t_HaxInt =
  {
    Core.Base.Spec.Haxint.f_v
    =
    Alloc.Borrow.Cow_Borrowed
    ((let list = [16uy] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list)
      <:
      t_Slice u8)
    <:
    Alloc.Borrow.t_Cow (t_Slice u8)
  }
  <:
  Core.Base.Spec.Haxint.t_HaxInt

let v_BITS_32_: Core.Base.Spec.Haxint.t_HaxInt =
  {
    Core.Base.Spec.Haxint.f_v
    =
    Alloc.Borrow.Cow_Borrowed
    ((let list = [32uy] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list)
      <:
      t_Slice u8)
    <:
    Alloc.Borrow.t_Cow (t_Slice u8)
  }
  <:
  Core.Base.Spec.Haxint.t_HaxInt

let v_BITS_64_: Core.Base.Spec.Haxint.t_HaxInt =
  {
    Core.Base.Spec.Haxint.f_v
    =
    Alloc.Borrow.Cow_Borrowed
    ((let list = [64uy] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list)
      <:
      t_Slice u8)
    <:
    Alloc.Borrow.t_Cow (t_Slice u8)
  }
  <:
  Core.Base.Spec.Haxint.t_HaxInt

let v_BITS_8_: Core.Base.Spec.Haxint.t_HaxInt =
  {
    Core.Base.Spec.Haxint.f_v
    =
    Alloc.Borrow.Cow_Borrowed
    ((let list = [8uy] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list)
      <:
      t_Slice u8)
    <:
    Alloc.Borrow.t_Cow (t_Slice u8)
  }
  <:
  Core.Base.Spec.Haxint.t_HaxInt

let v_WORDSIZE_128_: Core.Base.Spec.Haxint.t_HaxInt =
  {
    Core.Base.Spec.Haxint.f_v
    =
    Alloc.Borrow.Cow_Borrowed
    ((let list =
          [0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 1uy]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 17);
        Rust_primitives.Hax.array_of_list 17 list)
      <:
      t_Slice u8)
    <:
    Alloc.Borrow.t_Cow (t_Slice u8)
  }
  <:
  Core.Base.Spec.Haxint.t_HaxInt

let v_WORDSIZE_128_SUB_1_: Core.Base.Spec.Haxint.t_HaxInt =
  {
    Core.Base.Spec.Haxint.f_v
    =
    Alloc.Borrow.Cow_Borrowed
    ((let list =
          [
            255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy;
            255uy; 255uy; 255uy; 255uy
          ]
        in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
        Rust_primitives.Hax.array_of_list 16 list)
      <:
      t_Slice u8)
    <:
    Alloc.Borrow.t_Cow (t_Slice u8)
  }
  <:
  Core.Base.Spec.Haxint.t_HaxInt

let v_WORDSIZE_16_: Core.Base.Spec.Haxint.t_HaxInt =
  {
    Core.Base.Spec.Haxint.f_v
    =
    Alloc.Borrow.Cow_Borrowed
    ((let list = [0uy; 0uy; 1uy] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 3);
        Rust_primitives.Hax.array_of_list 3 list)
      <:
      t_Slice u8)
    <:
    Alloc.Borrow.t_Cow (t_Slice u8)
  }
  <:
  Core.Base.Spec.Haxint.t_HaxInt

let v_NEG_WORDSIZE_32_: Core.Base.Spec.Z.t_Z =
  Core.Base.Spec.Z.Z_NEG
  (Core.Base.Spec.Binary.Positive.Positive v_WORDSIZE_16_
    <:
    Core.Base.Spec.Binary.Positive.t_Positive)
  <:
  Core.Base.Spec.Z.t_Z

let v_WORDSIZE_16_SUB_1_: Core.Base.Spec.Haxint.t_HaxInt =
  {
    Core.Base.Spec.Haxint.f_v
    =
    Alloc.Borrow.Cow_Borrowed
    ((let list = [255uy; 255uy] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
      <:
      t_Slice u8)
    <:
    Alloc.Borrow.t_Cow (t_Slice u8)
  }
  <:
  Core.Base.Spec.Haxint.t_HaxInt

let v_POS_WORDSIZE_32_: Core.Base.Spec.Z.t_Z =
  Core.Base.Spec.Z.Z_POS
  (Core.Base.Spec.Binary.Positive.Positive v_WORDSIZE_16_SUB_1_
    <:
    Core.Base.Spec.Binary.Positive.t_Positive)
  <:
  Core.Base.Spec.Z.t_Z

let v_WORDSIZE_32_: Core.Base.Spec.Haxint.t_HaxInt =
  {
    Core.Base.Spec.Haxint.f_v
    =
    Alloc.Borrow.Cow_Borrowed
    ((let list = [0uy; 0uy; 0uy; 0uy; 1uy] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 5);
        Rust_primitives.Hax.array_of_list 5 list)
      <:
      t_Slice u8)
    <:
    Alloc.Borrow.t_Cow (t_Slice u8)
  }
  <:
  Core.Base.Spec.Haxint.t_HaxInt

let v_NEG_WORDSIZE_64_: Core.Base.Spec.Z.t_Z =
  Core.Base.Spec.Z.Z_NEG
  (Core.Base.Spec.Binary.Positive.Positive v_WORDSIZE_32_
    <:
    Core.Base.Spec.Binary.Positive.t_Positive)
  <:
  Core.Base.Spec.Z.t_Z

let v_WORDSIZE_32_SUB_1_: Core.Base.Spec.Haxint.t_HaxInt =
  {
    Core.Base.Spec.Haxint.f_v
    =
    Alloc.Borrow.Cow_Borrowed
    ((let list = [255uy; 255uy; 255uy; 255uy] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
        Rust_primitives.Hax.array_of_list 4 list)
      <:
      t_Slice u8)
    <:
    Alloc.Borrow.t_Cow (t_Slice u8)
  }
  <:
  Core.Base.Spec.Haxint.t_HaxInt

let v_POS_WORDSIZE_64_: Core.Base.Spec.Z.t_Z =
  Core.Base.Spec.Z.Z_POS
  (Core.Base.Spec.Binary.Positive.Positive v_WORDSIZE_32_SUB_1_
    <:
    Core.Base.Spec.Binary.Positive.t_Positive)
  <:
  Core.Base.Spec.Z.t_Z

let v_WORDSIZE_4_: Core.Base.Spec.Haxint.t_HaxInt =
  {
    Core.Base.Spec.Haxint.f_v
    =
    Alloc.Borrow.Cow_Borrowed
    ((let list = [128uy] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list)
      <:
      t_Slice u8)
    <:
    Alloc.Borrow.t_Cow (t_Slice u8)
  }
  <:
  Core.Base.Spec.Haxint.t_HaxInt

let v_NEG_WORDSIZE_8_: Core.Base.Spec.Z.t_Z =
  Core.Base.Spec.Z.Z_NEG
  (Core.Base.Spec.Binary.Positive.Positive v_WORDSIZE_4_
    <:
    Core.Base.Spec.Binary.Positive.t_Positive)
  <:
  Core.Base.Spec.Z.t_Z

let v_WORDSIZE_4_SUB_1_: Core.Base.Spec.Haxint.t_HaxInt =
  {
    Core.Base.Spec.Haxint.f_v
    =
    Alloc.Borrow.Cow_Borrowed
    ((let list = [127uy] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list)
      <:
      t_Slice u8)
    <:
    Alloc.Borrow.t_Cow (t_Slice u8)
  }
  <:
  Core.Base.Spec.Haxint.t_HaxInt

let v_POS_WORDSIZE_8_: Core.Base.Spec.Z.t_Z =
  Core.Base.Spec.Z.Z_POS
  (Core.Base.Spec.Binary.Positive.Positive v_WORDSIZE_4_SUB_1_
    <:
    Core.Base.Spec.Binary.Positive.t_Positive)
  <:
  Core.Base.Spec.Z.t_Z

let v_WORDSIZE_64_: Core.Base.Spec.Haxint.t_HaxInt =
  {
    Core.Base.Spec.Haxint.f_v
    =
    Alloc.Borrow.Cow_Borrowed
    ((let list = [0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 1uy] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 9);
        Rust_primitives.Hax.array_of_list 9 list)
      <:
      t_Slice u8)
    <:
    Alloc.Borrow.t_Cow (t_Slice u8)
  }
  <:
  Core.Base.Spec.Haxint.t_HaxInt

let v_NEG_WORDSIZE_128_: Core.Base.Spec.Z.t_Z =
  Core.Base.Spec.Z.Z_NEG
  (Core.Base.Spec.Binary.Positive.Positive v_WORDSIZE_64_
    <:
    Core.Base.Spec.Binary.Positive.t_Positive)
  <:
  Core.Base.Spec.Z.t_Z

let v_WORDSIZE_64_SUB_1_: Core.Base.Spec.Haxint.t_HaxInt =
  {
    Core.Base.Spec.Haxint.f_v
    =
    Alloc.Borrow.Cow_Borrowed
    ((let list = [255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy; 255uy] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
        Rust_primitives.Hax.array_of_list 8 list)
      <:
      t_Slice u8)
    <:
    Alloc.Borrow.t_Cow (t_Slice u8)
  }
  <:
  Core.Base.Spec.Haxint.t_HaxInt

let v_POS_WORDSIZE_128_: Core.Base.Spec.Z.t_Z =
  Core.Base.Spec.Z.Z_POS
  (Core.Base.Spec.Binary.Positive.Positive v_WORDSIZE_64_SUB_1_
    <:
    Core.Base.Spec.Binary.Positive.t_Positive)
  <:
  Core.Base.Spec.Z.t_Z

let v_WORDSIZE_8_: Core.Base.Spec.Haxint.t_HaxInt =
  {
    Core.Base.Spec.Haxint.f_v
    =
    Alloc.Borrow.Cow_Borrowed
    ((let list = [0uy; 1uy] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
      <:
      t_Slice u8)
    <:
    Alloc.Borrow.t_Cow (t_Slice u8)
  }
  <:
  Core.Base.Spec.Haxint.t_HaxInt

let v_NEG_WORDSIZE_16_: Core.Base.Spec.Z.t_Z =
  Core.Base.Spec.Z.Z_NEG
  (Core.Base.Spec.Binary.Positive.Positive v_WORDSIZE_8_
    <:
    Core.Base.Spec.Binary.Positive.t_Positive)
  <:
  Core.Base.Spec.Z.t_Z

let v_WORDSIZE_8_SUB_1_: Core.Base.Spec.Haxint.t_HaxInt =
  {
    Core.Base.Spec.Haxint.f_v
    =
    Alloc.Borrow.Cow_Borrowed
    ((let list = [255uy] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list)
      <:
      t_Slice u8)
    <:
    Alloc.Borrow.t_Cow (t_Slice u8)
  }
  <:
  Core.Base.Spec.Haxint.t_HaxInt

let v_POS_WORDSIZE_16_: Core.Base.Spec.Z.t_Z =
  Core.Base.Spec.Z.Z_POS
  (Core.Base.Spec.Binary.Positive.Positive v_WORDSIZE_8_SUB_1_
    <:
    Core.Base.Spec.Binary.Positive.t_Positive)
  <:
  Core.Base.Spec.Z.t_Z

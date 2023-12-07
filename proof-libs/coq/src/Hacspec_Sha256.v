(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition block_size_v : uint_size :=
  usize 64.

Definition len_size_v : uint_size :=
  usize 8.

Definition k_size_v : uint_size :=
  usize 64.

Definition hash_size_v : uint_size :=
  (usize 256) / (usize 8).

Definition block_t := nseq (uint8) (block_size_v).

Definition op_table_type_t := nseq (uint_size) (usize 12).

Definition sha256_digest_t := nseq (uint8) (hash_size_v).

Definition round_constants_table_t := nseq (uint32) (k_size_v).

Definition hash_t := nseq (uint32) (usize 8).

Definition ch (x_663 : uint32) (y_664 : uint32) (z_665 : uint32) : uint32 :=
  ((x_663) .& (y_664)) .^ ((not (x_663)) .& (z_665)).

Definition maj (x_666 : uint32) (y_667 : uint32) (z_668 : uint32) : uint32 :=
  ((x_666) .& (y_667)) .^ (((x_666) .& (z_668)) .^ ((y_667) .& (z_668))).

Definition op_table_v : op_table_type_t :=
  array_from_list uint_size (let l :=
      [
        usize 2;
        usize 13;
        usize 22;
        usize 6;
        usize 11;
        usize 25;
        usize 7;
        usize 18;
        usize 3;
        usize 17;
        usize 19;
        usize 10
      ] in  l).

Definition k_table_v : round_constants_table_t :=
  array_from_list uint32 (let l :=
      [
        secret (@repr WORDSIZE32 1116352408) : int32;
        secret (@repr WORDSIZE32 1899447441) : int32;
        secret (@repr WORDSIZE32 3049323471) : int32;
        secret (@repr WORDSIZE32 3921009573) : int32;
        secret (@repr WORDSIZE32 961987163) : int32;
        secret (@repr WORDSIZE32 1508970993) : int32;
        secret (@repr WORDSIZE32 2453635748) : int32;
        secret (@repr WORDSIZE32 2870763221) : int32;
        secret (@repr WORDSIZE32 3624381080) : int32;
        secret (@repr WORDSIZE32 310598401) : int32;
        secret (@repr WORDSIZE32 607225278) : int32;
        secret (@repr WORDSIZE32 1426881987) : int32;
        secret (@repr WORDSIZE32 1925078388) : int32;
        secret (@repr WORDSIZE32 2162078206) : int32;
        secret (@repr WORDSIZE32 2614888103) : int32;
        secret (@repr WORDSIZE32 3248222580) : int32;
        secret (@repr WORDSIZE32 3835390401) : int32;
        secret (@repr WORDSIZE32 4022224774) : int32;
        secret (@repr WORDSIZE32 264347078) : int32;
        secret (@repr WORDSIZE32 604807628) : int32;
        secret (@repr WORDSIZE32 770255983) : int32;
        secret (@repr WORDSIZE32 1249150122) : int32;
        secret (@repr WORDSIZE32 1555081692) : int32;
        secret (@repr WORDSIZE32 1996064986) : int32;
        secret (@repr WORDSIZE32 2554220882) : int32;
        secret (@repr WORDSIZE32 2821834349) : int32;
        secret (@repr WORDSIZE32 2952996808) : int32;
        secret (@repr WORDSIZE32 3210313671) : int32;
        secret (@repr WORDSIZE32 3336571891) : int32;
        secret (@repr WORDSIZE32 3584528711) : int32;
        secret (@repr WORDSIZE32 113926993) : int32;
        secret (@repr WORDSIZE32 338241895) : int32;
        secret (@repr WORDSIZE32 666307205) : int32;
        secret (@repr WORDSIZE32 773529912) : int32;
        secret (@repr WORDSIZE32 1294757372) : int32;
        secret (@repr WORDSIZE32 1396182291) : int32;
        secret (@repr WORDSIZE32 1695183700) : int32;
        secret (@repr WORDSIZE32 1986661051) : int32;
        secret (@repr WORDSIZE32 2177026350) : int32;
        secret (@repr WORDSIZE32 2456956037) : int32;
        secret (@repr WORDSIZE32 2730485921) : int32;
        secret (@repr WORDSIZE32 2820302411) : int32;
        secret (@repr WORDSIZE32 3259730800) : int32;
        secret (@repr WORDSIZE32 3345764771) : int32;
        secret (@repr WORDSIZE32 3516065817) : int32;
        secret (@repr WORDSIZE32 3600352804) : int32;
        secret (@repr WORDSIZE32 4094571909) : int32;
        secret (@repr WORDSIZE32 275423344) : int32;
        secret (@repr WORDSIZE32 430227734) : int32;
        secret (@repr WORDSIZE32 506948616) : int32;
        secret (@repr WORDSIZE32 659060556) : int32;
        secret (@repr WORDSIZE32 883997877) : int32;
        secret (@repr WORDSIZE32 958139571) : int32;
        secret (@repr WORDSIZE32 1322822218) : int32;
        secret (@repr WORDSIZE32 1537002063) : int32;
        secret (@repr WORDSIZE32 1747873779) : int32;
        secret (@repr WORDSIZE32 1955562222) : int32;
        secret (@repr WORDSIZE32 2024104815) : int32;
        secret (@repr WORDSIZE32 2227730452) : int32;
        secret (@repr WORDSIZE32 2361852424) : int32;
        secret (@repr WORDSIZE32 2428436474) : int32;
        secret (@repr WORDSIZE32 2756734187) : int32;
        secret (@repr WORDSIZE32 3204031479) : int32;
        secret (@repr WORDSIZE32 3329325298) : int32
      ] in  l).

Definition hash_init_v : hash_t :=
  array_from_list uint32 (let l :=
      [
        secret (@repr WORDSIZE32 1779033703) : int32;
        secret (@repr WORDSIZE32 3144134277) : int32;
        secret (@repr WORDSIZE32 1013904242) : int32;
        secret (@repr WORDSIZE32 2773480762) : int32;
        secret (@repr WORDSIZE32 1359893119) : int32;
        secret (@repr WORDSIZE32 2600822924) : int32;
        secret (@repr WORDSIZE32 528734635) : int32;
        secret (@repr WORDSIZE32 1541459225) : int32
      ] in  l).

Definition sigma
  (x_669 : uint32)
  (i_670 : uint_size)
  (op_671 : uint_size)
  : uint32 :=
  let tmp_672 : uint32 :=
    uint32_rotate_right (x_669) (array_index (op_table_v) (((usize 3) * (
            i_670)) + (usize 2))) in 
  let '(tmp_672) :=
    if (op_671) =.? (usize 0):bool then (let tmp_672 :=
        (x_669) shift_right (array_index (op_table_v) (((usize 3) * (i_670)) + (
              usize 2))) in 
      (tmp_672)) else ((tmp_672)) in 
  ((uint32_rotate_right (x_669) (array_index (op_table_v) ((usize 3) * (
            i_670)))) .^ (uint32_rotate_right (x_669) (array_index (
          op_table_v) (((usize 3) * (i_670)) + (usize 1))))) .^ (tmp_672).

Definition schedule (block_673 : block_t) : round_constants_table_t :=
  let b_674 : seq uint32 :=
    array_to_be_uint32s (block_673) in 
  let s_675 : round_constants_table_t :=
    array_new_ (default : uint32) (k_size_v) in 
  let s_675 :=
    foldi (usize 0) (k_size_v) (fun i_676 s_675 =>
      let '(s_675) :=
        if (i_676) <.? (usize 16):bool then (let s_675 :=
            array_upd s_675 (i_676) (seq_index (b_674) (i_676)) in 
          (s_675)) else (let t16_677 : uint32 :=
            array_index (s_675) ((i_676) - (usize 16)) in 
          let t15_678 : uint32 :=
            array_index (s_675) ((i_676) - (usize 15)) in 
          let t7_679 : uint32 :=
            array_index (s_675) ((i_676) - (usize 7)) in 
          let t2_680 : uint32 :=
            array_index (s_675) ((i_676) - (usize 2)) in 
          let s1_681 : uint32 :=
            sigma (t2_680) (usize 3) (usize 0) in 
          let s0_682 : uint32 :=
            sigma (t15_678) (usize 2) (usize 0) in 
          let s_675 :=
            array_upd s_675 (i_676) ((((s1_681) .+ (t7_679)) .+ (s0_682)) .+ (
                t16_677)) in 
          (s_675)) in 
      (s_675))
    s_675 in 
  s_675.

Definition shuffle
  (ws_683 : round_constants_table_t)
  (hashi_684 : hash_t)
  : hash_t :=
  let h_685 : hash_t :=
    hashi_684 in 
  let h_685 :=
    foldi (usize 0) (k_size_v) (fun i_686 h_685 =>
      let a0_687 : uint32 :=
        array_index (h_685) (usize 0) in 
      let b0_688 : uint32 :=
        array_index (h_685) (usize 1) in 
      let c0_689 : uint32 :=
        array_index (h_685) (usize 2) in 
      let d0_690 : uint32 :=
        array_index (h_685) (usize 3) in 
      let e0_691 : uint32 :=
        array_index (h_685) (usize 4) in 
      let f0_692 : uint32 :=
        array_index (h_685) (usize 5) in 
      let g0_693 : uint32 :=
        array_index (h_685) (usize 6) in 
      let h0_694 : uint32 :=
        array_index (h_685) (usize 7) in 
      let t1_695 : uint32 :=
        ((((h0_694) .+ (sigma (e0_691) (usize 1) (usize 1))) .+ (ch (e0_691) (
                f0_692) (g0_693))) .+ (array_index (k_table_v) (i_686))) .+ (
          array_index (ws_683) (i_686)) in 
      let t2_696 : uint32 :=
        (sigma (a0_687) (usize 0) (usize 1)) .+ (maj (a0_687) (b0_688) (
            c0_689)) in 
      let h_685 :=
        array_upd h_685 (usize 0) ((t1_695) .+ (t2_696)) in 
      let h_685 :=
        array_upd h_685 (usize 1) (a0_687) in 
      let h_685 :=
        array_upd h_685 (usize 2) (b0_688) in 
      let h_685 :=
        array_upd h_685 (usize 3) (c0_689) in 
      let h_685 :=
        array_upd h_685 (usize 4) ((d0_690) .+ (t1_695)) in 
      let h_685 :=
        array_upd h_685 (usize 5) (e0_691) in 
      let h_685 :=
        array_upd h_685 (usize 6) (f0_692) in 
      let h_685 :=
        array_upd h_685 (usize 7) (g0_693) in 
      (h_685))
    h_685 in 
  h_685.

Definition compress (block_697 : block_t) (h_in_698 : hash_t) : hash_t :=
  let s_699 : round_constants_table_t :=
    schedule (block_697) in 
  let h_700 : hash_t :=
    shuffle (s_699) (h_in_698) in 
  let h_700 :=
    foldi (usize 0) (usize 8) (fun i_701 h_700 =>
      let h_700 :=
        array_upd h_700 (i_701) ((array_index (h_700) (i_701)) .+ (array_index (
              h_in_698) (i_701))) in 
      (h_700))
    h_700 in 
  h_700.

Definition hash (msg_702 : byte_seq) : sha256_digest_t :=
  let h_703 : hash_t :=
    hash_init_v in 
  let last_block_704 : block_t :=
    array_new_ (default : uint8) (block_size_v) in 
  let last_block_len_705 : uint_size :=
    usize 0 in 
  let '(h_703, last_block_704, last_block_len_705) :=
    foldi (usize 0) (seq_num_chunks (msg_702) (block_size_v)) (fun i_706 '(
        h_703,
        last_block_704,
        last_block_len_705
      ) =>
      let '(block_len_707, block_708) :=
        seq_get_chunk (msg_702) (block_size_v) (i_706) in 
      let '(h_703, last_block_704, last_block_len_705) :=
        if (block_len_707) <.? (block_size_v):bool then (let last_block_704 :=
            array_update_start (array_new_ (default : uint8) (block_size_v)) (
              block_708) in 
          let last_block_len_705 :=
            block_len_707 in 
          (h_703, last_block_704, last_block_len_705)) else (
          let compress_input_709 : block_t :=
            array_from_seq (block_size_v) (block_708) in 
          let h_703 :=
            compress (compress_input_709) (h_703) in 
          (h_703, last_block_704, last_block_len_705)) in 
      (h_703, last_block_704, last_block_len_705))
    (h_703, last_block_704, last_block_len_705) in 
  let last_block_704 :=
    array_upd last_block_704 (last_block_len_705) (secret (
        @repr WORDSIZE8 128) : int8) in 
  let len_bist_710 : uint64 :=
    secret (pub_u64 ((seq_len (msg_702)) * (usize 8))) : int64 in 
  let '(h_703, last_block_704) :=
    if (last_block_len_705) <.? ((block_size_v) - (len_size_v)):bool then (
      let last_block_704 :=
        array_update (last_block_704) ((block_size_v) - (len_size_v)) (
          array_to_seq (uint64_to_be_bytes (len_bist_710))) in 
      let h_703 :=
        compress (last_block_704) (h_703) in 
      (h_703, last_block_704)) else (let pad_block_711 : block_t :=
        array_new_ (default : uint8) (block_size_v) in 
      let pad_block_711 :=
        array_update (pad_block_711) ((block_size_v) - (len_size_v)) (
          array_to_seq (uint64_to_be_bytes (len_bist_710))) in 
      let h_703 :=
        compress (last_block_704) (h_703) in 
      let h_703 :=
        compress (pad_block_711) (h_703) in 
      (h_703, last_block_704)) in 
  array_from_seq (hash_size_v) (array_to_be_bytes (h_703)).

Definition sha256 (msg_712 : byte_seq) : sha256_digest_t :=
  hash (msg_712).


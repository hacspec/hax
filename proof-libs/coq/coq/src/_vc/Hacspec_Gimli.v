(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition state_t := nseq (uint32) (usize 12).

Definition state_idx_t :=
  nat_mod (usize 12).
Definition uint_size_in_state_idx_t(n : uint_size) : state_idx_t := int_in_nat_mod n.
Coercion uint_size_in_state_idx_t : uint_size >-> state_idx_t.

Definition swap
  (s_757 : state_t)
  (i_758 : state_idx_t)
  (j_759 : state_idx_t)
  : state_t :=
  let tmp_760 : uint32 :=
    array_index (s_757) (i_758) in 
  let s_757 :=
    array_upd s_757 (i_758) (array_index (s_757) (j_759)) in 
  let s_757 :=
    array_upd s_757 (j_759) (tmp_760) in 
  s_757.

Definition gimli_round (s_761 : state_t) (r_762 : int32) : state_t :=
  let s_761 :=
    foldi (usize 0) (usize 4) (fun col_763 s_761 =>
      let x_764 : uint32 :=
        uint32_rotate_left (array_index (s_761) (col_763)) (usize 24) in 
      let y_765 : uint32 :=
        uint32_rotate_left (array_index (s_761) ((col_763) + (usize 4))) (
          usize 9) in 
      let z_766 : uint32 :=
        array_index (s_761) ((col_763) + (usize 8)) in 
      let s_761 :=
        array_upd s_761 ((col_763) + (usize 8)) (((x_764) .^ ((
                z_766) shift_left (usize 1))) .^ (((y_765) .& (
                z_766)) shift_left (usize 2))) in 
      let s_761 :=
        array_upd s_761 ((col_763) + (usize 4)) (((y_765) .^ (x_764)) .^ (((
                x_764) .| (z_766)) shift_left (usize 1))) in 
      let s_761 :=
        array_upd s_761 (col_763) (((z_766) .^ (y_765)) .^ (((x_764) .& (
                y_765)) shift_left (usize 3))) in 
      (s_761))
    s_761 in 
  let '(s_761) :=
    if ((r_762) .& (@repr WORDSIZE32 3)) =.? (@repr WORDSIZE32 0):bool then (
      let s_761 :=
        swap (s_761) (usize 0) (usize 1) in 
      let s_761 :=
        swap (s_761) (usize 2) (usize 3) in 
      (s_761)) else ((s_761)) in 
  let '(s_761) :=
    if ((r_762) .& (@repr WORDSIZE32 3)) =.? (@repr WORDSIZE32 2):bool then (
      let s_761 :=
        swap (s_761) (usize 0) (usize 2) in 
      let s_761 :=
        swap (s_761) (usize 1) (usize 3) in 
      (s_761)) else ((s_761)) in 
  let '(s_761) :=
    if ((r_762) .& (@repr WORDSIZE32 3)) =.? (@repr WORDSIZE32 0):bool then (
      let s_761 :=
        array_upd s_761 (usize 0) ((array_index (s_761) (usize 0)) .^ ((secret (
                @repr WORDSIZE32 2654435584) : int32) .| (secret (
                r_762) : int32))) in 
      (s_761)) else ((s_761)) in 
  s_761.

Definition gimli (s_767 : state_t) : state_t :=
  let s_767 :=
    foldi (usize 0) (usize 24) (fun rnd_768 s_767 =>
      let rnd_769 : int32 :=
        pub_u32 ((usize 24) - (rnd_768)) in 
      let s_767 :=
        gimli_round (s_767) (rnd_769) in 
      (s_767))
    s_767 in 
  s_767.

Definition block_t := nseq (uint8) (usize 16).

Definition digest_t := nseq (uint8) (usize 32).

Definition absorb_block
  (input_block_770 : block_t)
  (s_771 : state_t)
  : state_t :=
  let input_bytes_772 : seq uint32 :=
    array_to_le_uint32s (input_block_770) in 
  let s_771 :=
    array_upd s_771 (usize 0) ((array_index (s_771) (usize 0)) .^ (seq_index (
          input_bytes_772) (usize 0))) in 
  let s_771 :=
    array_upd s_771 (usize 1) ((array_index (s_771) (usize 1)) .^ (seq_index (
          input_bytes_772) (usize 1))) in 
  let s_771 :=
    array_upd s_771 (usize 2) ((array_index (s_771) (usize 2)) .^ (seq_index (
          input_bytes_772) (usize 2))) in 
  let s_771 :=
    array_upd s_771 (usize 3) ((array_index (s_771) (usize 3)) .^ (seq_index (
          input_bytes_772) (usize 3))) in 
  gimli (s_771).

Definition squeeze_block (s_773 : state_t) : block_t :=
  let block_774 : block_t :=
    array_new_ (default) (16) in 
  let block_774 :=
    foldi (usize 0) (usize 4) (fun i_775 block_774 =>
      let s_i_776 : uint32 :=
        array_index (s_773) (i_775) in 
      let s_i_bytes_777 : seq uint8 :=
        uint32_to_le_bytes (s_i_776) in 
      let block_774 :=
        array_upd block_774 ((usize 4) * (i_775)) (seq_index (s_i_bytes_777) (
            usize 0)) in 
      let block_774 :=
        array_upd block_774 (((usize 4) * (i_775)) + (usize 1)) (seq_index (
            s_i_bytes_777) (usize 1)) in 
      let block_774 :=
        array_upd block_774 (((usize 4) * (i_775)) + (usize 2)) (seq_index (
            s_i_bytes_777) (usize 2)) in 
      let block_774 :=
        array_upd block_774 (((usize 4) * (i_775)) + (usize 3)) (seq_index (
            s_i_bytes_777) (usize 3)) in 
      (block_774))
    block_774 in 
  block_774.

Definition gimli_hash_state
  (input_778 : byte_seq)
  (s_779 : state_t)
  : state_t :=
  let rate_780 : uint_size :=
    array_length  in 
  let chunks_781 : uint_size :=
    seq_num_exact_chunks (input_778) (rate_780) in 
  let s_779 :=
    foldi (usize 0) (chunks_781) (fun i_782 s_779 =>
      let input_block_783 : seq uint8 :=
        seq_get_exact_chunk (input_778) (rate_780) (i_782) in 
      let full_block_784 : block_t :=
        array_from_seq (16) (input_block_783) in 
      let s_779 :=
        absorb_block (full_block_784) (s_779) in 
      (s_779))
    s_779 in 
  let input_block_785 : seq uint8 :=
    seq_get_remainder_chunk (input_778) (rate_780) in 
  let input_block_padded_786 : block_t :=
    array_new_ (default) (16) in 
  let input_block_padded_787 : block_t :=
    array_update_start (input_block_padded_786) (input_block_785) in 
  let input_block_padded_787 :=
    array_upd input_block_padded_787 (seq_len (input_block_785)) (secret (
        @repr WORDSIZE8 1) : int8) in 
  let s_779 :=
    array_upd s_779 (usize 11) ((array_index (s_779) (usize 11)) .^ (secret (
          @repr WORDSIZE32 16777216) : int32)) in 
  let s_779 :=
    absorb_block (input_block_padded_787) (s_779) in 
  s_779.

Definition gimli_hash (input_bytes_788 : byte_seq) : digest_t :=
  let s_789 : state_t :=
    array_new_ (default) (12) in 
  let s_790 : state_t :=
    gimli_hash_state (input_bytes_788) (s_789) in 
  let output_791 : digest_t :=
    array_new_ (default) (32) in 
  let output_792 : digest_t :=
    array_update_start (output_791) (array_to_seq (squeeze_block (s_790))) in 
  let s_793 : state_t :=
    gimli (s_790) in 
  array_update (output_792) (array_length ) (array_to_seq (squeeze_block (
      s_793))).

Definition nonce_t := nseq (uint8) (usize 16).

Definition key_t := nseq (uint8) (usize 32).

Definition tag_t := nseq (uint8) (usize 16).

Definition process_ad (ad_794 : byte_seq) (s_795 : state_t) : state_t :=
  gimli_hash_state (ad_794) (s_795).

Definition process_msg
  (message_796 : byte_seq)
  (s_797 : state_t)
  : (state_t × byte_seq) :=
  let ciphertext_798 : seq uint8 :=
    seq_new_ (default) (seq_len (message_796)) in 
  let rate_799 : uint_size :=
    array_length  in 
  let num_chunks_800 : uint_size :=
    seq_num_exact_chunks (message_796) (rate_799) in 
  let '(s_797, ciphertext_798) :=
    foldi (usize 0) (num_chunks_800) (fun i_801 '(s_797, ciphertext_798) =>
      let key_block_802 : block_t :=
        squeeze_block (s_797) in 
      let msg_block_803 : seq uint8 :=
        seq_get_exact_chunk (message_796) (rate_799) (i_801) in 
      let msg_block_804 : block_t :=
        array_from_seq (16) (msg_block_803) in 
      let ciphertext_798 :=
        seq_set_exact_chunk (ciphertext_798) (rate_799) (i_801) (array_to_seq ((
            msg_block_804) array_xor (key_block_802))) in 
      let s_797 :=
        absorb_block (msg_block_804) (s_797) in 
      (s_797, ciphertext_798))
    (s_797, ciphertext_798) in 
  let key_block_805 : block_t :=
    squeeze_block (s_797) in 
  let last_block_806 : seq uint8 :=
    seq_get_remainder_chunk (message_796) (rate_799) in 
  let block_len_807 : uint_size :=
    seq_len (last_block_806) in 
  let msg_block_padded_808 : block_t :=
    array_new_ (default) (16) in 
  let msg_block_padded_809 : block_t :=
    array_update_start (msg_block_padded_808) (last_block_806) in 
  let ciphertext_798 :=
    seq_set_chunk (ciphertext_798) (rate_799) (num_chunks_800) (
      array_slice_range ((msg_block_padded_809) array_xor (key_block_805)) ((
          usize 0,
          block_len_807
        ))) in 
  let msg_block_padded_809 :=
    array_upd msg_block_padded_809 (block_len_807) ((array_index (
          msg_block_padded_809) (block_len_807)) .^ (secret (
          @repr WORDSIZE8 1) : int8)) in 
  let s_797 :=
    array_upd s_797 (usize 11) ((array_index (s_797) (usize 11)) .^ (secret (
          @repr WORDSIZE32 16777216) : int32)) in 
  let s_797 :=
    absorb_block (msg_block_padded_809) (s_797) in 
  (s_797, ciphertext_798).

Definition process_ct
  (ciphertext_810 : byte_seq)
  (s_811 : state_t)
  : (state_t × byte_seq) :=
  let message_812 : seq uint8 :=
    seq_new_ (default) (seq_len (ciphertext_810)) in 
  let rate_813 : uint_size :=
    array_length  in 
  let num_chunks_814 : uint_size :=
    seq_num_exact_chunks (ciphertext_810) (rate_813) in 
  let '(s_811, message_812) :=
    foldi (usize 0) (num_chunks_814) (fun i_815 '(s_811, message_812) =>
      let key_block_816 : block_t :=
        squeeze_block (s_811) in 
      let ct_block_817 : seq uint8 :=
        seq_get_exact_chunk (ciphertext_810) (rate_813) (i_815) in 
      let ct_block_818 : block_t :=
        array_from_seq (16) (ct_block_817) in 
      let msg_block_819 : block_t :=
        (ct_block_818) array_xor (key_block_816) in 
      let message_812 :=
        seq_set_exact_chunk (message_812) (rate_813) (i_815) (array_to_seq ((
            ct_block_818) array_xor (key_block_816))) in 
      let s_811 :=
        absorb_block (msg_block_819) (s_811) in 
      (s_811, message_812))
    (s_811, message_812) in 
  let key_block_820 : block_t :=
    squeeze_block (s_811) in 
  let ct_final_821 : seq uint8 :=
    seq_get_remainder_chunk (ciphertext_810) (rate_813) in 
  let block_len_822 : uint_size :=
    seq_len (ct_final_821) in 
  let ct_block_padded_823 : block_t :=
    array_new_ (default) (16) in 
  let ct_block_padded_824 : block_t :=
    array_update_start (ct_block_padded_823) (ct_final_821) in 
  let msg_block_825 : block_t :=
    (ct_block_padded_824) array_xor (key_block_820) in 
  let message_812 :=
    seq_set_chunk (message_812) (rate_813) (num_chunks_814) (array_slice_range (
        msg_block_825) ((usize 0, block_len_822))) in 
  let msg_block_826 : block_t :=
    array_from_slice_range (default) (16) (array_to_seq (msg_block_825)) ((
        usize 0,
        block_len_822
      )) in 
  let msg_block_826 :=
    array_upd msg_block_826 (block_len_822) ((array_index (msg_block_826) (
          block_len_822)) .^ (secret (@repr WORDSIZE8 1) : int8)) in 
  let s_811 :=
    array_upd s_811 (usize 11) ((array_index (s_811) (usize 11)) .^ (secret (
          @repr WORDSIZE32 16777216) : int32)) in 
  let s_811 :=
    absorb_block (msg_block_826) (s_811) in 
  (s_811, message_812).

Definition nonce_to_u32s (nonce_827 : nonce_t) : seq uint32 :=
  let uints_828 : seq uint32 :=
    seq_new_ (default) (usize 4) in 
  let uints_828 :=
    seq_upd uints_828 (usize 0) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (array_to_seq (nonce_827)) ((usize 0, usize 4)))) in 
  let uints_828 :=
    seq_upd uints_828 (usize 1) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (array_to_seq (nonce_827)) ((usize 4, usize 8)))) in 
  let uints_828 :=
    seq_upd uints_828 (usize 2) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (array_to_seq (nonce_827)) ((usize 8, usize 12)))) in 
  let uints_828 :=
    seq_upd uints_828 (usize 3) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (array_to_seq (nonce_827)) ((usize 12, usize 16)))) in 
  uints_828.

Definition key_to_u32s (key_829 : key_t) : seq uint32 :=
  let uints_830 : seq uint32 :=
    seq_new_ (default) (usize 8) in 
  let uints_830 :=
    seq_upd uints_830 (usize 0) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (array_to_seq (key_829)) ((usize 0, usize 4)))) in 
  let uints_830 :=
    seq_upd uints_830 (usize 1) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (array_to_seq (key_829)) ((usize 4, usize 8)))) in 
  let uints_830 :=
    seq_upd uints_830 (usize 2) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (array_to_seq (key_829)) ((usize 8, usize 12)))) in 
  let uints_830 :=
    seq_upd uints_830 (usize 3) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (array_to_seq (key_829)) ((usize 12, usize 16)))) in 
  let uints_830 :=
    seq_upd uints_830 (usize 4) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (array_to_seq (key_829)) ((usize 16, usize 20)))) in 
  let uints_830 :=
    seq_upd uints_830 (usize 5) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (array_to_seq (key_829)) ((usize 20, usize 24)))) in 
  let uints_830 :=
    seq_upd uints_830 (usize 6) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (array_to_seq (key_829)) ((usize 24, usize 28)))) in 
  let uints_830 :=
    seq_upd uints_830 (usize 7) (uint32_from_le_bytes (array_from_slice_range (
          default) (4) (array_to_seq (key_829)) ((usize 28, usize 32)))) in 
  uints_830.

Definition gimli_aead_encrypt
  (message_831 : byte_seq)
  (ad_832 : byte_seq)
  (nonce_833 : nonce_t)
  (key_834 : key_t)
  : (byte_seq × tag_t) :=
  let s_835 : state_t :=
    array_from_seq (12) (seq_concat (nonce_to_u32s (nonce_833)) (key_to_u32s (
          key_834))) in 
  let s_836 : state_t :=
    gimli (s_835) in 
  let s_837 : state_t :=
    process_ad (ad_832) (s_836) in 
  let '(s_838, ciphertext_839) :=
    process_msg (message_831) (s_837) in 
  let tag_840 : block_t :=
    squeeze_block (s_838) in 
  let tag_841 : tag_t :=
    array_from_seq (16) (array_to_seq (tag_840)) in 
  (ciphertext_839, tag_841).

Definition gimli_aead_decrypt
  (ciphertext_842 : byte_seq)
  (ad_843 : byte_seq)
  (tag_844 : tag_t)
  (nonce_845 : nonce_t)
  (key_846 : key_t)
  : byte_seq :=
  let s_847 : state_t :=
    array_from_seq (12) (seq_concat (nonce_to_u32s (nonce_845)) (key_to_u32s (
          key_846))) in 
  let s_848 : state_t :=
    gimli (s_847) in 
  let s_849 : state_t :=
    process_ad (ad_843) (s_848) in 
  let '(s_850, message_851) :=
    process_ct (ciphertext_842) (s_849) in 
  let my_tag_852 : block_t :=
    squeeze_block (s_850) in 
  let my_tag_853 : tag_t :=
    array_from_seq (16) (array_to_seq (my_tag_852)) in 
  let out_854 : seq uint8 :=
    seq_new_ (default) (usize 0) in 
  let '(out_854) :=
    if array_equal (my_tag_853) (tag_844):bool then (let out_854 :=
        message_851 in 
      (out_854)) else ((out_854)) in 
  out_854.


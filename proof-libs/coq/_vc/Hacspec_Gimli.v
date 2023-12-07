(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
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
  (s_1127 : state_t)
  (i_1128 : state_idx_t)
  (j_1129 : state_idx_t)
  : state_t :=
  let tmp_1130 : uint32 :=
    array_index (s_1127) (i_1128) in 
  let s_1127 :=
    array_upd s_1127 (i_1128) (array_index (s_1127) (j_1129)) in 
  let s_1127 :=
    array_upd s_1127 (j_1129) (tmp_1130) in 
  s_1127.

Definition gimli_round (s_1131 : state_t) (r_1132 : int32) : state_t :=
  let s_1131 :=
    foldi (usize 0) (usize 4) (fun col_1133 s_1131 =>
      let x_1134 : uint32 :=
        uint32_rotate_left (array_index (s_1131) (col_1133)) (usize 24) in 
      let y_1135 : uint32 :=
        uint32_rotate_left (array_index (s_1131) ((col_1133) + (usize 4))) (
          usize 9) in 
      let z_1136 : uint32 :=
        array_index (s_1131) ((col_1133) + (usize 8)) in 
      let s_1131 :=
        array_upd s_1131 ((col_1133) + (usize 8)) (((x_1134) .^ ((
                z_1136) shift_left (usize 1))) .^ (((y_1135) .& (
                z_1136)) shift_left (usize 2))) in 
      let s_1131 :=
        array_upd s_1131 ((col_1133) + (usize 4)) (((y_1135) .^ (x_1134)) .^ (((
                x_1134) .| (z_1136)) shift_left (usize 1))) in 
      let s_1131 :=
        array_upd s_1131 (col_1133) (((z_1136) .^ (y_1135)) .^ (((x_1134) .& (
                y_1135)) shift_left (usize 3))) in 
      (s_1131))
    s_1131 in 
  let '(s_1131) :=
    if ((r_1132) .& (@repr WORDSIZE32 3)) =.? (@repr WORDSIZE32 0):bool then (
      let s_1131 :=
        swap (s_1131) (usize 0) (usize 1) in 
      let s_1131 :=
        swap (s_1131) (usize 2) (usize 3) in 
      (s_1131)) else ((s_1131)) in 
  let '(s_1131) :=
    if ((r_1132) .& (@repr WORDSIZE32 3)) =.? (@repr WORDSIZE32 2):bool then (
      let s_1131 :=
        swap (s_1131) (usize 0) (usize 2) in 
      let s_1131 :=
        swap (s_1131) (usize 1) (usize 3) in 
      (s_1131)) else ((s_1131)) in 
  let '(s_1131) :=
    if ((r_1132) .& (@repr WORDSIZE32 3)) =.? (@repr WORDSIZE32 0):bool then (
      let s_1131 :=
        array_upd s_1131 (usize 0) ((array_index (s_1131) (usize 0)) .^ ((
              secret (@repr WORDSIZE32 2654435584) : int32) .| (secret (
                r_1132) : int32))) in 
      (s_1131)) else ((s_1131)) in 
  s_1131.

Definition gimli (s_1137 : state_t) : state_t :=
  let s_1137 :=
    foldi (usize 0) (usize 24) (fun rnd_1138 s_1137 =>
      let rnd_1139 : int32 :=
        pub_u32 ((usize 24) - (rnd_1138)) in 
      let s_1137 :=
        gimli_round (s_1137) (rnd_1139) in 
      (s_1137))
    s_1137 in 
  s_1137.

Definition block_t := nseq (uint8) (usize 16).

Definition digest_t := nseq (uint8) (usize 32).

Definition absorb_block
  (input_block_1140 : block_t)
  (s_1141 : state_t)
  : state_t :=
  let input_bytes_1142 : seq uint32 :=
    array_to_le_uint32s (input_block_1140) in 
  let s_1141 :=
    array_upd s_1141 (usize 0) ((array_index (s_1141) (usize 0)) .^ (seq_index (
          input_bytes_1142) (usize 0))) in 
  let s_1141 :=
    array_upd s_1141 (usize 1) ((array_index (s_1141) (usize 1)) .^ (seq_index (
          input_bytes_1142) (usize 1))) in 
  let s_1141 :=
    array_upd s_1141 (usize 2) ((array_index (s_1141) (usize 2)) .^ (seq_index (
          input_bytes_1142) (usize 2))) in 
  let s_1141 :=
    array_upd s_1141 (usize 3) ((array_index (s_1141) (usize 3)) .^ (seq_index (
          input_bytes_1142) (usize 3))) in 
  gimli (s_1141).

Definition squeeze_block (s_1143 : state_t) : block_t :=
  let block_1144 : block_t :=
    array_new_ (default : uint8) (16) in 
  let block_1144 :=
    foldi (usize 0) (usize 4) (fun i_1145 block_1144 =>
      let s_i_1146 : uint32 :=
        array_index (s_1143) (i_1145) in 
      let s_i_bytes_1147 : seq uint8 :=
        uint32_to_le_bytes (s_i_1146) in 
      let block_1144 :=
        array_upd block_1144 ((usize 4) * (i_1145)) (seq_index (
            s_i_bytes_1147) (usize 0)) in 
      let block_1144 :=
        array_upd block_1144 (((usize 4) * (i_1145)) + (usize 1)) (seq_index (
            s_i_bytes_1147) (usize 1)) in 
      let block_1144 :=
        array_upd block_1144 (((usize 4) * (i_1145)) + (usize 2)) (seq_index (
            s_i_bytes_1147) (usize 2)) in 
      let block_1144 :=
        array_upd block_1144 (((usize 4) * (i_1145)) + (usize 3)) (seq_index (
            s_i_bytes_1147) (usize 3)) in 
      (block_1144))
    block_1144 in 
  block_1144.

Definition gimli_hash_state
  (input_1148 : byte_seq)
  (s_1149 : state_t)
  : state_t :=
  let rate_1150 : uint_size :=
    array_length  in 
  let chunks_1151 : uint_size :=
    seq_num_exact_chunks (input_1148) (rate_1150) in 
  let s_1149 :=
    foldi (usize 0) (chunks_1151) (fun i_1152 s_1149 =>
      let input_block_1153 : seq uint8 :=
        seq_get_exact_chunk (input_1148) (rate_1150) (i_1152) in 
      let full_block_1154 : block_t :=
        array_from_seq (16) (input_block_1153) in 
      let s_1149 :=
        absorb_block (full_block_1154) (s_1149) in 
      (s_1149))
    s_1149 in 
  let input_block_1155 : seq uint8 :=
    seq_get_remainder_chunk (input_1148) (rate_1150) in 
  let input_block_padded_1156 : block_t :=
    array_new_ (default : uint8) (16) in 
  let input_block_padded_1157 : block_t :=
    array_update_start (input_block_padded_1156) (input_block_1155) in 
  let input_block_padded_1157 :=
    array_upd input_block_padded_1157 (seq_len (input_block_1155)) (secret (
        @repr WORDSIZE8 1) : int8) in 
  let s_1149 :=
    array_upd s_1149 (usize 11) ((array_index (s_1149) (usize 11)) .^ (secret (
          @repr WORDSIZE32 16777216) : int32)) in 
  let s_1149 :=
    absorb_block (input_block_padded_1157) (s_1149) in 
  s_1149.

Definition gimli_hash (input_bytes_1158 : byte_seq) : digest_t :=
  let s_1159 : state_t :=
    array_new_ (default : uint32) (12) in 
  let s_1160 : state_t :=
    gimli_hash_state (input_bytes_1158) (s_1159) in 
  let output_1161 : digest_t :=
    array_new_ (default : uint8) (32) in 
  let output_1162 : digest_t :=
    array_update_start (output_1161) (array_to_seq (squeeze_block (s_1160))) in 
  let s_1163 : state_t :=
    gimli (s_1160) in 
  array_update (output_1162) (array_length ) (array_to_seq (squeeze_block (
      s_1163))).

Definition nonce_t := nseq (uint8) (usize 16).

Definition key_t := nseq (uint8) (usize 32).

Definition tag_t := nseq (uint8) (usize 16).

Definition process_ad (ad_1164 : byte_seq) (s_1165 : state_t) : state_t :=
  gimli_hash_state (ad_1164) (s_1165).

Definition process_msg
  (message_1166 : byte_seq)
  (s_1167 : state_t)
  : (state_t '× byte_seq) :=
  let ciphertext_1168 : seq uint8 :=
    seq_new_ (default : uint8) (seq_len (message_1166)) in 
  let rate_1169 : uint_size :=
    array_length  in 
  let num_chunks_1170 : uint_size :=
    seq_num_exact_chunks (message_1166) (rate_1169) in 
  let '(s_1167, ciphertext_1168) :=
    foldi (usize 0) (num_chunks_1170) (fun i_1171 '(s_1167, ciphertext_1168) =>
      let key_block_1172 : block_t :=
        squeeze_block (s_1167) in 
      let msg_block_1173 : seq uint8 :=
        seq_get_exact_chunk (message_1166) (rate_1169) (i_1171) in 
      let msg_block_1174 : block_t :=
        array_from_seq (16) (msg_block_1173) in 
      let ciphertext_1168 :=
        seq_set_exact_chunk (ciphertext_1168) (rate_1169) (i_1171) (
          array_to_seq ((msg_block_1174) array_xor (key_block_1172))) in 
      let s_1167 :=
        absorb_block (msg_block_1174) (s_1167) in 
      (s_1167, ciphertext_1168))
    (s_1167, ciphertext_1168) in 
  let key_block_1175 : block_t :=
    squeeze_block (s_1167) in 
  let last_block_1176 : seq uint8 :=
    seq_get_remainder_chunk (message_1166) (rate_1169) in 
  let block_len_1177 : uint_size :=
    seq_len (last_block_1176) in 
  let msg_block_padded_1178 : block_t :=
    array_new_ (default : uint8) (16) in 
  let msg_block_padded_1179 : block_t :=
    array_update_start (msg_block_padded_1178) (last_block_1176) in 
  let ciphertext_1168 :=
    seq_set_chunk (ciphertext_1168) (rate_1169) (num_chunks_1170) (
      array_slice_range ((msg_block_padded_1179) array_xor (key_block_1175)) ((
          usize 0,
          block_len_1177
        ))) in 
  let msg_block_padded_1179 :=
    array_upd msg_block_padded_1179 (block_len_1177) ((array_index (
          msg_block_padded_1179) (block_len_1177)) .^ (secret (
          @repr WORDSIZE8 1) : int8)) in 
  let s_1167 :=
    array_upd s_1167 (usize 11) ((array_index (s_1167) (usize 11)) .^ (secret (
          @repr WORDSIZE32 16777216) : int32)) in 
  let s_1167 :=
    absorb_block (msg_block_padded_1179) (s_1167) in 
  (s_1167, ciphertext_1168).

Definition process_ct
  (ciphertext_1180 : byte_seq)
  (s_1181 : state_t)
  : (state_t '× byte_seq) :=
  let message_1182 : seq uint8 :=
    seq_new_ (default : uint8) (seq_len (ciphertext_1180)) in 
  let rate_1183 : uint_size :=
    array_length  in 
  let num_chunks_1184 : uint_size :=
    seq_num_exact_chunks (ciphertext_1180) (rate_1183) in 
  let '(s_1181, message_1182) :=
    foldi (usize 0) (num_chunks_1184) (fun i_1185 '(s_1181, message_1182) =>
      let key_block_1186 : block_t :=
        squeeze_block (s_1181) in 
      let ct_block_1187 : seq uint8 :=
        seq_get_exact_chunk (ciphertext_1180) (rate_1183) (i_1185) in 
      let ct_block_1188 : block_t :=
        array_from_seq (16) (ct_block_1187) in 
      let msg_block_1189 : block_t :=
        (ct_block_1188) array_xor (key_block_1186) in 
      let message_1182 :=
        seq_set_exact_chunk (message_1182) (rate_1183) (i_1185) (array_to_seq ((
            ct_block_1188) array_xor (key_block_1186))) in 
      let s_1181 :=
        absorb_block (msg_block_1189) (s_1181) in 
      (s_1181, message_1182))
    (s_1181, message_1182) in 
  let key_block_1190 : block_t :=
    squeeze_block (s_1181) in 
  let ct_final_1191 : seq uint8 :=
    seq_get_remainder_chunk (ciphertext_1180) (rate_1183) in 
  let block_len_1192 : uint_size :=
    seq_len (ct_final_1191) in 
  let ct_block_padded_1193 : block_t :=
    array_new_ (default : uint8) (16) in 
  let ct_block_padded_1194 : block_t :=
    array_update_start (ct_block_padded_1193) (ct_final_1191) in 
  let msg_block_1195 : block_t :=
    (ct_block_padded_1194) array_xor (key_block_1190) in 
  let message_1182 :=
    seq_set_chunk (message_1182) (rate_1183) (num_chunks_1184) (
      array_slice_range (msg_block_1195) ((usize 0, block_len_1192))) in 
  let msg_block_1196 : block_t :=
    array_from_slice_range (default : uint8) (16) (
      array_to_seq (msg_block_1195)) ((usize 0, block_len_1192)) in 
  let msg_block_1196 :=
    array_upd msg_block_1196 (block_len_1192) ((array_index (msg_block_1196) (
          block_len_1192)) .^ (secret (@repr WORDSIZE8 1) : int8)) in 
  let s_1181 :=
    array_upd s_1181 (usize 11) ((array_index (s_1181) (usize 11)) .^ (secret (
          @repr WORDSIZE32 16777216) : int32)) in 
  let s_1181 :=
    absorb_block (msg_block_1196) (s_1181) in 
  (s_1181, message_1182).

Definition nonce_to_u32s (nonce_1197 : nonce_t) : seq uint32 :=
  let uints_1198 : seq uint32 :=
    seq_new_ (default : uint32) (usize 4) in 
  let uints_1198 :=
    seq_upd uints_1198 (usize 0) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (nonce_1197)) ((usize 0, usize 4
          )))) in 
  let uints_1198 :=
    seq_upd uints_1198 (usize 1) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (nonce_1197)) ((usize 4, usize 8
          )))) in 
  let uints_1198 :=
    seq_upd uints_1198 (usize 2) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (nonce_1197)) ((usize 8, usize 12
          )))) in 
  let uints_1198 :=
    seq_upd uints_1198 (usize 3) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (nonce_1197)) ((usize 12, usize 16
          )))) in 
  uints_1198.

Definition key_to_u32s (key_1199 : key_t) : seq uint32 :=
  let uints_1200 : seq uint32 :=
    seq_new_ (default : uint32) (usize 8) in 
  let uints_1200 :=
    seq_upd uints_1200 (usize 0) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (key_1199)) ((usize 0, usize 4
          )))) in 
  let uints_1200 :=
    seq_upd uints_1200 (usize 1) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (key_1199)) ((usize 4, usize 8
          )))) in 
  let uints_1200 :=
    seq_upd uints_1200 (usize 2) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (key_1199)) ((usize 8, usize 12
          )))) in 
  let uints_1200 :=
    seq_upd uints_1200 (usize 3) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (key_1199)) ((usize 12, usize 16
          )))) in 
  let uints_1200 :=
    seq_upd uints_1200 (usize 4) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (key_1199)) ((usize 16, usize 20
          )))) in 
  let uints_1200 :=
    seq_upd uints_1200 (usize 5) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (key_1199)) ((usize 20, usize 24
          )))) in 
  let uints_1200 :=
    seq_upd uints_1200 (usize 6) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (key_1199)) ((usize 24, usize 28
          )))) in 
  let uints_1200 :=
    seq_upd uints_1200 (usize 7) (uint32_from_le_bytes (array_from_slice_range (
          default : uint8) (4) (array_to_seq (key_1199)) ((usize 28, usize 32
          )))) in 
  uints_1200.

Definition gimli_aead_encrypt
  (message_1201 : byte_seq)
  (ad_1202 : byte_seq)
  (nonce_1203 : nonce_t)
  (key_1204 : key_t)
  : (byte_seq '× tag_t) :=
  let s_1205 : state_t :=
    array_from_seq (12) (seq_concat (nonce_to_u32s (nonce_1203)) (key_to_u32s (
          key_1204))) in 
  let s_1206 : state_t :=
    gimli (s_1205) in 
  let s_1207 : state_t :=
    process_ad (ad_1202) (s_1206) in 
  let '(s_1208, ciphertext_1209) :=
    process_msg (message_1201) (s_1207) in 
  let tag_1210 : block_t :=
    squeeze_block (s_1208) in 
  let tag_1211 : tag_t :=
    array_from_seq (16) (array_to_seq (tag_1210)) in 
  (ciphertext_1209, tag_1211).

Definition gimli_aead_decrypt
  (ciphertext_1212 : byte_seq)
  (ad_1213 : byte_seq)
  (tag_1214 : tag_t)
  (nonce_1215 : nonce_t)
  (key_1216 : key_t)
  : byte_seq :=
  let s_1217 : state_t :=
    array_from_seq (12) (seq_concat (nonce_to_u32s (nonce_1215)) (key_to_u32s (
          key_1216))) in 
  let s_1218 : state_t :=
    gimli (s_1217) in 
  let s_1219 : state_t :=
    process_ad (ad_1213) (s_1218) in 
  let '(s_1220, message_1221) :=
    process_ct (ciphertext_1212) (s_1219) in 
  let my_tag_1222 : block_t :=
    squeeze_block (s_1220) in 
  let my_tag_1223 : tag_t :=
    array_from_seq (16) (array_to_seq (my_tag_1222)) in 
  let out_1224 : seq uint8 :=
    seq_new_ (default : uint8) (usize 0) in 
  let '(out_1224) :=
    if array_equal (my_tag_1223) (tag_1214):bool then (let out_1224 :=
        message_1221 in 
      (out_1224)) else ((out_1224)) in 
  out_1224.


(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition blocksize_v : uint_size :=
  usize 16.

Definition ivsize_v : uint_size :=
  usize 12.

Definition key_length_v : uint_size :=
  usize 4.

Definition rounds_v : uint_size :=
  usize 10.

Definition key_schedule_length_v : uint_size :=
  usize 176.

Definition iterations_v : uint_size :=
  usize 40.

Definition invalid_key_expansion_index_v : int8 :=
  @repr WORDSIZE8 1.

Definition block_t := nseq (uint8) (blocksize_v).

Definition word_t := nseq (uint8) (key_length_v).

Definition round_key_t := nseq (uint8) (blocksize_v).

Definition aes_nonce_t := nseq (uint8) (ivsize_v).

Definition s_box_t := nseq (uint8) (usize 256).

Definition r_con_t := nseq (uint8) (usize 15).

Definition bytes144_t := nseq (uint8) (usize 144).

Definition bytes176_t := nseq (uint8) (key_schedule_length_v).

Definition key128_t := nseq (uint8) (blocksize_v).

Notation "'byte_seq_result_t'" := ((result byte_seq int8)) : hacspec_scope.

Notation "'block_result_t'" := ((result block_t int8)) : hacspec_scope.

Notation "'word_result_t'" := ((result word_t int8)) : hacspec_scope.

Definition sbox_v : s_box_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 99) : int8;
        secret (@repr WORDSIZE8 124) : int8;
        secret (@repr WORDSIZE8 119) : int8;
        secret (@repr WORDSIZE8 123) : int8;
        secret (@repr WORDSIZE8 242) : int8;
        secret (@repr WORDSIZE8 107) : int8;
        secret (@repr WORDSIZE8 111) : int8;
        secret (@repr WORDSIZE8 197) : int8;
        secret (@repr WORDSIZE8 48) : int8;
        secret (@repr WORDSIZE8 1) : int8;
        secret (@repr WORDSIZE8 103) : int8;
        secret (@repr WORDSIZE8 43) : int8;
        secret (@repr WORDSIZE8 254) : int8;
        secret (@repr WORDSIZE8 215) : int8;
        secret (@repr WORDSIZE8 171) : int8;
        secret (@repr WORDSIZE8 118) : int8;
        secret (@repr WORDSIZE8 202) : int8;
        secret (@repr WORDSIZE8 130) : int8;
        secret (@repr WORDSIZE8 201) : int8;
        secret (@repr WORDSIZE8 125) : int8;
        secret (@repr WORDSIZE8 250) : int8;
        secret (@repr WORDSIZE8 89) : int8;
        secret (@repr WORDSIZE8 71) : int8;
        secret (@repr WORDSIZE8 240) : int8;
        secret (@repr WORDSIZE8 173) : int8;
        secret (@repr WORDSIZE8 212) : int8;
        secret (@repr WORDSIZE8 162) : int8;
        secret (@repr WORDSIZE8 175) : int8;
        secret (@repr WORDSIZE8 156) : int8;
        secret (@repr WORDSIZE8 164) : int8;
        secret (@repr WORDSIZE8 114) : int8;
        secret (@repr WORDSIZE8 192) : int8;
        secret (@repr WORDSIZE8 183) : int8;
        secret (@repr WORDSIZE8 253) : int8;
        secret (@repr WORDSIZE8 147) : int8;
        secret (@repr WORDSIZE8 38) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 63) : int8;
        secret (@repr WORDSIZE8 247) : int8;
        secret (@repr WORDSIZE8 204) : int8;
        secret (@repr WORDSIZE8 52) : int8;
        secret (@repr WORDSIZE8 165) : int8;
        secret (@repr WORDSIZE8 229) : int8;
        secret (@repr WORDSIZE8 241) : int8;
        secret (@repr WORDSIZE8 113) : int8;
        secret (@repr WORDSIZE8 216) : int8;
        secret (@repr WORDSIZE8 49) : int8;
        secret (@repr WORDSIZE8 21) : int8;
        secret (@repr WORDSIZE8 4) : int8;
        secret (@repr WORDSIZE8 199) : int8;
        secret (@repr WORDSIZE8 35) : int8;
        secret (@repr WORDSIZE8 195) : int8;
        secret (@repr WORDSIZE8 24) : int8;
        secret (@repr WORDSIZE8 150) : int8;
        secret (@repr WORDSIZE8 5) : int8;
        secret (@repr WORDSIZE8 154) : int8;
        secret (@repr WORDSIZE8 7) : int8;
        secret (@repr WORDSIZE8 18) : int8;
        secret (@repr WORDSIZE8 128) : int8;
        secret (@repr WORDSIZE8 226) : int8;
        secret (@repr WORDSIZE8 235) : int8;
        secret (@repr WORDSIZE8 39) : int8;
        secret (@repr WORDSIZE8 178) : int8;
        secret (@repr WORDSIZE8 117) : int8;
        secret (@repr WORDSIZE8 9) : int8;
        secret (@repr WORDSIZE8 131) : int8;
        secret (@repr WORDSIZE8 44) : int8;
        secret (@repr WORDSIZE8 26) : int8;
        secret (@repr WORDSIZE8 27) : int8;
        secret (@repr WORDSIZE8 110) : int8;
        secret (@repr WORDSIZE8 90) : int8;
        secret (@repr WORDSIZE8 160) : int8;
        secret (@repr WORDSIZE8 82) : int8;
        secret (@repr WORDSIZE8 59) : int8;
        secret (@repr WORDSIZE8 214) : int8;
        secret (@repr WORDSIZE8 179) : int8;
        secret (@repr WORDSIZE8 41) : int8;
        secret (@repr WORDSIZE8 227) : int8;
        secret (@repr WORDSIZE8 47) : int8;
        secret (@repr WORDSIZE8 132) : int8;
        secret (@repr WORDSIZE8 83) : int8;
        secret (@repr WORDSIZE8 209) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 237) : int8;
        secret (@repr WORDSIZE8 32) : int8;
        secret (@repr WORDSIZE8 252) : int8;
        secret (@repr WORDSIZE8 177) : int8;
        secret (@repr WORDSIZE8 91) : int8;
        secret (@repr WORDSIZE8 106) : int8;
        secret (@repr WORDSIZE8 203) : int8;
        secret (@repr WORDSIZE8 190) : int8;
        secret (@repr WORDSIZE8 57) : int8;
        secret (@repr WORDSIZE8 74) : int8;
        secret (@repr WORDSIZE8 76) : int8;
        secret (@repr WORDSIZE8 88) : int8;
        secret (@repr WORDSIZE8 207) : int8;
        secret (@repr WORDSIZE8 208) : int8;
        secret (@repr WORDSIZE8 239) : int8;
        secret (@repr WORDSIZE8 170) : int8;
        secret (@repr WORDSIZE8 251) : int8;
        secret (@repr WORDSIZE8 67) : int8;
        secret (@repr WORDSIZE8 77) : int8;
        secret (@repr WORDSIZE8 51) : int8;
        secret (@repr WORDSIZE8 133) : int8;
        secret (@repr WORDSIZE8 69) : int8;
        secret (@repr WORDSIZE8 249) : int8;
        secret (@repr WORDSIZE8 2) : int8;
        secret (@repr WORDSIZE8 127) : int8;
        secret (@repr WORDSIZE8 80) : int8;
        secret (@repr WORDSIZE8 60) : int8;
        secret (@repr WORDSIZE8 159) : int8;
        secret (@repr WORDSIZE8 168) : int8;
        secret (@repr WORDSIZE8 81) : int8;
        secret (@repr WORDSIZE8 163) : int8;
        secret (@repr WORDSIZE8 64) : int8;
        secret (@repr WORDSIZE8 143) : int8;
        secret (@repr WORDSIZE8 146) : int8;
        secret (@repr WORDSIZE8 157) : int8;
        secret (@repr WORDSIZE8 56) : int8;
        secret (@repr WORDSIZE8 245) : int8;
        secret (@repr WORDSIZE8 188) : int8;
        secret (@repr WORDSIZE8 182) : int8;
        secret (@repr WORDSIZE8 218) : int8;
        secret (@repr WORDSIZE8 33) : int8;
        secret (@repr WORDSIZE8 16) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 243) : int8;
        secret (@repr WORDSIZE8 210) : int8;
        secret (@repr WORDSIZE8 205) : int8;
        secret (@repr WORDSIZE8 12) : int8;
        secret (@repr WORDSIZE8 19) : int8;
        secret (@repr WORDSIZE8 236) : int8;
        secret (@repr WORDSIZE8 95) : int8;
        secret (@repr WORDSIZE8 151) : int8;
        secret (@repr WORDSIZE8 68) : int8;
        secret (@repr WORDSIZE8 23) : int8;
        secret (@repr WORDSIZE8 196) : int8;
        secret (@repr WORDSIZE8 167) : int8;
        secret (@repr WORDSIZE8 126) : int8;
        secret (@repr WORDSIZE8 61) : int8;
        secret (@repr WORDSIZE8 100) : int8;
        secret (@repr WORDSIZE8 93) : int8;
        secret (@repr WORDSIZE8 25) : int8;
        secret (@repr WORDSIZE8 115) : int8;
        secret (@repr WORDSIZE8 96) : int8;
        secret (@repr WORDSIZE8 129) : int8;
        secret (@repr WORDSIZE8 79) : int8;
        secret (@repr WORDSIZE8 220) : int8;
        secret (@repr WORDSIZE8 34) : int8;
        secret (@repr WORDSIZE8 42) : int8;
        secret (@repr WORDSIZE8 144) : int8;
        secret (@repr WORDSIZE8 136) : int8;
        secret (@repr WORDSIZE8 70) : int8;
        secret (@repr WORDSIZE8 238) : int8;
        secret (@repr WORDSIZE8 184) : int8;
        secret (@repr WORDSIZE8 20) : int8;
        secret (@repr WORDSIZE8 222) : int8;
        secret (@repr WORDSIZE8 94) : int8;
        secret (@repr WORDSIZE8 11) : int8;
        secret (@repr WORDSIZE8 219) : int8;
        secret (@repr WORDSIZE8 224) : int8;
        secret (@repr WORDSIZE8 50) : int8;
        secret (@repr WORDSIZE8 58) : int8;
        secret (@repr WORDSIZE8 10) : int8;
        secret (@repr WORDSIZE8 73) : int8;
        secret (@repr WORDSIZE8 6) : int8;
        secret (@repr WORDSIZE8 36) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 194) : int8;
        secret (@repr WORDSIZE8 211) : int8;
        secret (@repr WORDSIZE8 172) : int8;
        secret (@repr WORDSIZE8 98) : int8;
        secret (@repr WORDSIZE8 145) : int8;
        secret (@repr WORDSIZE8 149) : int8;
        secret (@repr WORDSIZE8 228) : int8;
        secret (@repr WORDSIZE8 121) : int8;
        secret (@repr WORDSIZE8 231) : int8;
        secret (@repr WORDSIZE8 200) : int8;
        secret (@repr WORDSIZE8 55) : int8;
        secret (@repr WORDSIZE8 109) : int8;
        secret (@repr WORDSIZE8 141) : int8;
        secret (@repr WORDSIZE8 213) : int8;
        secret (@repr WORDSIZE8 78) : int8;
        secret (@repr WORDSIZE8 169) : int8;
        secret (@repr WORDSIZE8 108) : int8;
        secret (@repr WORDSIZE8 86) : int8;
        secret (@repr WORDSIZE8 244) : int8;
        secret (@repr WORDSIZE8 234) : int8;
        secret (@repr WORDSIZE8 101) : int8;
        secret (@repr WORDSIZE8 122) : int8;
        secret (@repr WORDSIZE8 174) : int8;
        secret (@repr WORDSIZE8 8) : int8;
        secret (@repr WORDSIZE8 186) : int8;
        secret (@repr WORDSIZE8 120) : int8;
        secret (@repr WORDSIZE8 37) : int8;
        secret (@repr WORDSIZE8 46) : int8;
        secret (@repr WORDSIZE8 28) : int8;
        secret (@repr WORDSIZE8 166) : int8;
        secret (@repr WORDSIZE8 180) : int8;
        secret (@repr WORDSIZE8 198) : int8;
        secret (@repr WORDSIZE8 232) : int8;
        secret (@repr WORDSIZE8 221) : int8;
        secret (@repr WORDSIZE8 116) : int8;
        secret (@repr WORDSIZE8 31) : int8;
        secret (@repr WORDSIZE8 75) : int8;
        secret (@repr WORDSIZE8 189) : int8;
        secret (@repr WORDSIZE8 139) : int8;
        secret (@repr WORDSIZE8 138) : int8;
        secret (@repr WORDSIZE8 112) : int8;
        secret (@repr WORDSIZE8 62) : int8;
        secret (@repr WORDSIZE8 181) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 72) : int8;
        secret (@repr WORDSIZE8 3) : int8;
        secret (@repr WORDSIZE8 246) : int8;
        secret (@repr WORDSIZE8 14) : int8;
        secret (@repr WORDSIZE8 97) : int8;
        secret (@repr WORDSIZE8 53) : int8;
        secret (@repr WORDSIZE8 87) : int8;
        secret (@repr WORDSIZE8 185) : int8;
        secret (@repr WORDSIZE8 134) : int8;
        secret (@repr WORDSIZE8 193) : int8;
        secret (@repr WORDSIZE8 29) : int8;
        secret (@repr WORDSIZE8 158) : int8;
        secret (@repr WORDSIZE8 225) : int8;
        secret (@repr WORDSIZE8 248) : int8;
        secret (@repr WORDSIZE8 152) : int8;
        secret (@repr WORDSIZE8 17) : int8;
        secret (@repr WORDSIZE8 105) : int8;
        secret (@repr WORDSIZE8 217) : int8;
        secret (@repr WORDSIZE8 142) : int8;
        secret (@repr WORDSIZE8 148) : int8;
        secret (@repr WORDSIZE8 155) : int8;
        secret (@repr WORDSIZE8 30) : int8;
        secret (@repr WORDSIZE8 135) : int8;
        secret (@repr WORDSIZE8 233) : int8;
        secret (@repr WORDSIZE8 206) : int8;
        secret (@repr WORDSIZE8 85) : int8;
        secret (@repr WORDSIZE8 40) : int8;
        secret (@repr WORDSIZE8 223) : int8;
        secret (@repr WORDSIZE8 140) : int8;
        secret (@repr WORDSIZE8 161) : int8;
        secret (@repr WORDSIZE8 137) : int8;
        secret (@repr WORDSIZE8 13) : int8;
        secret (@repr WORDSIZE8 191) : int8;
        secret (@repr WORDSIZE8 230) : int8;
        secret (@repr WORDSIZE8 66) : int8;
        secret (@repr WORDSIZE8 104) : int8;
        secret (@repr WORDSIZE8 65) : int8;
        secret (@repr WORDSIZE8 153) : int8;
        secret (@repr WORDSIZE8 45) : int8;
        secret (@repr WORDSIZE8 15) : int8;
        secret (@repr WORDSIZE8 176) : int8;
        secret (@repr WORDSIZE8 84) : int8;
        secret (@repr WORDSIZE8 187) : int8;
        secret (@repr WORDSIZE8 22) : int8
      ] in  l).

Definition rcon_v : r_con_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 141) : int8;
        secret (@repr WORDSIZE8 1) : int8;
        secret (@repr WORDSIZE8 2) : int8;
        secret (@repr WORDSIZE8 4) : int8;
        secret (@repr WORDSIZE8 8) : int8;
        secret (@repr WORDSIZE8 16) : int8;
        secret (@repr WORDSIZE8 32) : int8;
        secret (@repr WORDSIZE8 64) : int8;
        secret (@repr WORDSIZE8 128) : int8;
        secret (@repr WORDSIZE8 27) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 108) : int8;
        secret (@repr WORDSIZE8 216) : int8;
        secret (@repr WORDSIZE8 171) : int8;
        secret (@repr WORDSIZE8 77) : int8
      ] in  l).

Definition sub_bytes (state_150 : block_t) : block_t :=
  let st_151 : block_t :=
    state_150 in 
  let st_151 :=
    foldi (usize 0) (blocksize_v) (fun i_152 st_151 =>
      let st_151 :=
        array_upd st_151 (i_152) (array_index (sbox_v) (uint8_declassify (
              array_index (state_150) (i_152)))) in 
      (st_151))
    st_151 in 
  st_151.

Definition shift_row
  (i_153 : uint_size)
  (shift_154 : uint_size)
  (state_155 : block_t)
  : block_t :=
  let out_156 : block_t :=
    state_155 in 
  let out_156 :=
    array_upd out_156 (i_153) (array_index (state_155) ((i_153) + ((usize 4) * (
            (shift_154) %% (usize 4))))) in 
  let out_156 :=
    array_upd out_156 ((i_153) + (usize 4)) (array_index (state_155) ((
          i_153) + ((usize 4) * (((shift_154) + (usize 1)) %% (usize 4))))) in 
  let out_156 :=
    array_upd out_156 ((i_153) + (usize 8)) (array_index (state_155) ((
          i_153) + ((usize 4) * (((shift_154) + (usize 2)) %% (usize 4))))) in 
  let out_156 :=
    array_upd out_156 ((i_153) + (usize 12)) (array_index (state_155) ((
          i_153) + ((usize 4) * (((shift_154) + (usize 3)) %% (usize 4))))) in 
  out_156.

Definition shift_rows (state_157 : block_t) : block_t :=
  let state_158 : block_t :=
    shift_row (usize 1) (usize 1) (state_157) in 
  let state_159 : block_t :=
    shift_row (usize 2) (usize 2) (state_158) in 
  shift_row (usize 3) (usize 3) (state_159).

Definition xtime (x_160 : uint8) : uint8 :=
  let x1_161 : uint8 :=
    (x_160) shift_left (usize 1) in 
  let x7_162 : uint8 :=
    (x_160) shift_right (usize 7) in 
  let x71_163 : uint8 :=
    (x7_162) .& (secret (@repr WORDSIZE8 1) : int8) in 
  let x711b_164 : uint8 :=
    (x71_163) .* (secret (@repr WORDSIZE8 27) : int8) in 
  (x1_161) .^ (x711b_164).

Definition mix_column (c_165 : uint_size) (state_166 : block_t) : block_t :=
  let i0_167 : uint_size :=
    (usize 4) * (c_165) in 
  let s0_168 : uint8 :=
    array_index (state_166) (i0_167) in 
  let s1_169 : uint8 :=
    array_index (state_166) ((i0_167) + (usize 1)) in 
  let s2_170 : uint8 :=
    array_index (state_166) ((i0_167) + (usize 2)) in 
  let s3_171 : uint8 :=
    array_index (state_166) ((i0_167) + (usize 3)) in 
  let st_172 : block_t :=
    state_166 in 
  let tmp_173 : uint8 :=
    (((s0_168) .^ (s1_169)) .^ (s2_170)) .^ (s3_171) in 
  let st_172 :=
    array_upd st_172 (i0_167) (((s0_168) .^ (tmp_173)) .^ (xtime ((s0_168) .^ (
            s1_169)))) in 
  let st_172 :=
    array_upd st_172 ((i0_167) + (usize 1)) (((s1_169) .^ (tmp_173)) .^ (xtime (
          (s1_169) .^ (s2_170)))) in 
  let st_172 :=
    array_upd st_172 ((i0_167) + (usize 2)) (((s2_170) .^ (tmp_173)) .^ (xtime (
          (s2_170) .^ (s3_171)))) in 
  let st_172 :=
    array_upd st_172 ((i0_167) + (usize 3)) (((s3_171) .^ (tmp_173)) .^ (xtime (
          (s3_171) .^ (s0_168)))) in 
  st_172.

Definition mix_columns (state_174 : block_t) : block_t :=
  let state_175 : block_t :=
    mix_column (usize 0) (state_174) in 
  let state_176 : block_t :=
    mix_column (usize 1) (state_175) in 
  let state_177 : block_t :=
    mix_column (usize 2) (state_176) in 
  mix_column (usize 3) (state_177).

Definition add_round_key
  (state_178 : block_t)
  (key_179 : round_key_t)
  : block_t :=
  let out_180 : block_t :=
    state_178 in 
  let out_180 :=
    foldi (usize 0) (blocksize_v) (fun i_181 out_180 =>
      let out_180 :=
        array_upd out_180 (i_181) ((array_index (out_180) (i_181)) .^ (
            array_index (key_179) (i_181))) in 
      (out_180))
    out_180 in 
  out_180.

Definition aes_enc
  (state_182 : block_t)
  (round_key_183 : round_key_t)
  : block_t :=
  let state_184 : block_t :=
    sub_bytes (state_182) in 
  let state_185 : block_t :=
    shift_rows (state_184) in 
  let state_186 : block_t :=
    mix_columns (state_185) in 
  add_round_key (state_186) (round_key_183).

Definition aes_enc_last
  (state_187 : block_t)
  (round_key_188 : round_key_t)
  : block_t :=
  let state_189 : block_t :=
    sub_bytes (state_187) in 
  let state_190 : block_t :=
    shift_rows (state_189) in 
  add_round_key (state_190) (round_key_188).

Definition rounds_aes (state_191 : block_t) (key_192 : byte_seq) : block_t :=
  let out_193 : block_t :=
    state_191 in 
  let out_193 :=
    foldi (usize 0) (seq_num_chunks (key_192) (
          blocksize_v)) (fun i_194 out_193 =>
      let '(_, key_block_195) :=
        seq_get_chunk (key_192) (blocksize_v) (i_194) in 
      let out_193 :=
        aes_enc (out_193) (array_from_seq (blocksize_v) (key_block_195)) in 
      (out_193))
    out_193 in 
  out_193.

Definition block_cipher_aes
  (input_196 : block_t)
  (key_197 : byte_seq)
  (nr_198 : uint_size)
  : block_t :=
  let k0_199 : round_key_t :=
    array_from_slice_range (default : uint8) (blocksize_v) (key_197) ((
        usize 0,
        usize 16
      )) in 
  let k_200 : seq uint8 :=
    seq_from_slice_range (key_197) ((usize 16, (nr_198) * (usize 16))) in 
  let kn_201 : round_key_t :=
    array_from_slice (default : uint8) (blocksize_v) (key_197) ((nr_198) * (
        usize 16)) (usize 16) in 
  let state_202 : block_t :=
    add_round_key (input_196) (k0_199) in 
  let state_203 : block_t :=
    rounds_aes (state_202) (k_200) in 
  aes_enc_last (state_203) (kn_201).

Definition rotate_word (w_204 : word_t) : word_t :=
  array_from_list uint8 (let l :=
      [
        array_index (w_204) (usize 1);
        array_index (w_204) (usize 2);
        array_index (w_204) (usize 3);
        array_index (w_204) (usize 0)
      ] in  l).

Definition slice_word (w_205 : word_t) : word_t :=
  array_from_list uint8 (let l :=
      [
        array_index (sbox_v) (declassify_usize_from_uint8 (array_index (w_205) (
              usize 0)));
        array_index (sbox_v) (declassify_usize_from_uint8 (array_index (w_205) (
              usize 1)));
        array_index (sbox_v) (declassify_usize_from_uint8 (array_index (w_205) (
              usize 2)));
        array_index (sbox_v) (declassify_usize_from_uint8 (array_index (w_205) (
              usize 3)))
      ] in  l).

Definition aes_keygen_assist (w_206 : word_t) (rcon_207 : uint8) : word_t :=
  let k_208 : word_t :=
    rotate_word (w_206) in 
  let k_208 :=
    slice_word (k_208) in 
  let k_208 :=
    array_upd k_208 (usize 0) ((array_index (k_208) (usize 0)) .^ (
        rcon_207)) in 
  k_208.

Definition key_expansion_word
  (w0_209 : word_t)
  (w1_210 : word_t)
  (i_211 : uint_size)
  (nk_212 : uint_size)
  (nr_213 : uint_size)
  : word_result_t :=
  let k_214 : word_t :=
    w1_210 in 
  let result_215 : (result word_t int8) :=
    @Err word_t int8 (invalid_key_expansion_index_v) in 
  let '(k_214, result_215) :=
    if (i_211) <.? ((usize 4) * ((nr_213) + (usize 1))):bool then (let '(k_214
        ) :=
        if ((i_211) %% (nk_212)) =.? (usize 0):bool then (let k_214 :=
            aes_keygen_assist (k_214) (array_index (rcon_v) ((i_211) / (
                  nk_212))) in 
          (k_214)) else (let '(k_214) :=
            if ((nk_212) >.? (usize 6)) && (((i_211) %% (nk_212)) =.? (
                usize 4)):bool then (let k_214 :=
                slice_word (k_214) in 
              (k_214)) else ((k_214)) in 
          (k_214)) in 
      let k_214 :=
        foldi (usize 0) (usize 4) (fun i_216 k_214 =>
          let k_214 :=
            array_upd k_214 (i_216) ((array_index (k_214) (i_216)) .^ (
                array_index (w0_209) (i_216))) in 
          (k_214))
        k_214 in 
      let result_215 :=
        @Ok word_t int8 (k_214) in 
      (k_214, result_215)) else ((k_214, result_215)) in 
  result_215.

Definition key_expansion_aes
  (key_217 : byte_seq)
  (nk_218 : uint_size)
  (nr_219 : uint_size)
  (key_schedule_length_220 : uint_size)
  (key_length_221 : uint_size)
  (iterations_222 : uint_size)
  : byte_seq_result_t :=
  let key_ex_223 : seq uint8 :=
    seq_new_ (default : uint8) (key_schedule_length_220) in 
  let key_ex_223 :=
    seq_update_start (key_ex_223) (key_217) in 
  let word_size_224 : uint_size :=
    key_length_221 in 
  bind (foldibnd (usize 0) to (
      iterations_222) for key_ex_223 >> (fun j_225 key_ex_223 =>
    let i_226 : uint_size :=
      (j_225) + (word_size_224) in 
    bind (key_expansion_word (array_from_slice (default : uint8) (
          key_length_v) (key_ex_223) ((usize 4) * ((i_226) - (word_size_224))) (
          usize 4)) (array_from_slice (default : uint8) (key_length_v) (
          key_ex_223) (((usize 4) * (i_226)) - (usize 4)) (usize 4)) (i_226) (
        nk_218) (nr_219)) (fun word_227 => let key_ex_223 :=
        seq_update (key_ex_223) ((usize 4) * (i_226)) (
          array_to_seq (word_227)) in 
      @Ok (seq uint8) int8 ((key_ex_223))))) (fun key_ex_223 =>
    @Ok byte_seq int8 (key_ex_223)).

Definition aes_encrypt_block
  (k_228 : byte_seq)
  (input_229 : block_t)
  (nk_230 : uint_size)
  (nr_231 : uint_size)
  (key_schedule_length_232 : uint_size)
  (key_length_233 : uint_size)
  (iterations_234 : uint_size)
  : block_result_t :=
  bind (key_expansion_aes (k_228) (nk_230) (nr_231) (key_schedule_length_232) (
      key_length_233) (iterations_234)) (fun key_ex_235 => @Ok block_t int8 (
      block_cipher_aes (input_229) (key_ex_235) (nr_231))).

Definition aes128_encrypt_block
  (k_236 : key128_t)
  (input_237 : block_t)
  : block_t :=
  result_unwrap (aes_encrypt_block (seq_from_seq (array_to_seq (k_236))) (
      input_237) (key_length_v) (rounds_v) (key_schedule_length_v) (
      key_length_v) (iterations_v)).

Definition aes_ctr_key_block
  (k_238 : byte_seq)
  (n_239 : aes_nonce_t)
  (c_240 : uint32)
  (nk_241 : uint_size)
  (nr_242 : uint_size)
  (key_schedule_length_243 : uint_size)
  (key_length_244 : uint_size)
  (iterations_245 : uint_size)
  : block_result_t :=
  let input_246 : block_t :=
    array_new_ (default : uint8) (blocksize_v) in 
  let input_246 :=
    array_update (input_246) (usize 0) (array_to_seq (n_239)) in 
  let input_246 :=
    array_update (input_246) (usize 12) (array_to_seq (uint32_to_be_bytes (
        c_240))) in 
  aes_encrypt_block (k_238) (input_246) (nk_241) (nr_242) (
    key_schedule_length_243) (key_length_244) (iterations_245).

Definition xor_block
  (block_247 : block_t)
  (key_block_248 : block_t)
  : block_t :=
  let out_249 : block_t :=
    block_247 in 
  let out_249 :=
    foldi (usize 0) (blocksize_v) (fun i_250 out_249 =>
      let out_249 :=
        array_upd out_249 (i_250) ((array_index (out_249) (i_250)) .^ (
            array_index (key_block_248) (i_250))) in 
      (out_249))
    out_249 in 
  out_249.

Definition aes_counter_mode
  (key_251 : byte_seq)
  (nonce_252 : aes_nonce_t)
  (counter_253 : uint32)
  (msg_254 : byte_seq)
  (nk_255 : uint_size)
  (nr_256 : uint_size)
  (key_schedule_length_257 : uint_size)
  (key_length_258 : uint_size)
  (iterations_259 : uint_size)
  : byte_seq_result_t :=
  let ctr_260 : uint32 :=
    counter_253 in 
  let blocks_out_261 : seq uint8 :=
    seq_new_ (default : uint8) (seq_len (msg_254)) in 
  let n_blocks_262 : uint_size :=
    seq_num_exact_chunks (msg_254) (blocksize_v) in 
  bind (foldibnd (usize 0) to (n_blocks_262) for (ctr_260, blocks_out_261
    ) >> (fun i_263 '(ctr_260, blocks_out_261) =>
    let msg_block_264 : seq uint8 :=
      seq_get_exact_chunk (msg_254) (blocksize_v) (i_263) in 
    bind (aes_ctr_key_block (key_251) (nonce_252) (ctr_260) (nk_255) (nr_256) (
        key_schedule_length_257) (key_length_258) (iterations_259)) (
      fun key_block_265 => let blocks_out_261 :=
        seq_set_chunk (blocks_out_261) (blocksize_v) (i_263) (
          array_to_seq (xor_block (array_from_seq (blocksize_v) (
              msg_block_264)) (key_block_265))) in 
      let ctr_260 :=
        (ctr_260) .+ (secret (@repr WORDSIZE32 1) : int32) in 
      @Ok (uint32 '× seq uint8) int8 ((ctr_260, blocks_out_261))))) (fun '(
      ctr_260,
      blocks_out_261
    ) => let last_block_266 : seq uint8 :=
      seq_get_remainder_chunk (msg_254) (blocksize_v) in 
    let last_block_len_267 : uint_size :=
      seq_len (last_block_266) in 
    ifbnd (last_block_len_267) !=.? (usize 0) : bool
    thenbnd (let last_block_268 : block_t :=
        array_update_start (array_new_ (default : uint8) (blocksize_v)) (
          last_block_266) in 
      bind (aes_ctr_key_block (key_251) (nonce_252) (ctr_260) (nk_255) (
          nr_256) (key_schedule_length_257) (key_length_258) (iterations_259)) (
        fun key_block_269 => let blocks_out_261 :=
          seq_set_chunk (blocks_out_261) (blocksize_v) (n_blocks_262) (
            array_slice_range (xor_block (last_block_268) (key_block_269)) ((
                usize 0,
                last_block_len_267
              ))) in 
        @Ok (seq uint8) int8 ((blocks_out_261))))
    else ((blocks_out_261)) >> (fun '(blocks_out_261) =>
    @Ok byte_seq int8 (blocks_out_261))).

Definition aes128_encrypt
  (key_270 : key128_t)
  (nonce_271 : aes_nonce_t)
  (counter_272 : uint32)
  (msg_273 : byte_seq)
  : byte_seq :=
  result_unwrap (aes_counter_mode (seq_from_seq (array_to_seq (key_270))) (
      nonce_271) (counter_272) (msg_273) (key_length_v) (rounds_v) (
      key_schedule_length_v) (key_length_v) (iterations_v)).

Definition aes128_decrypt
  (key_274 : key128_t)
  (nonce_275 : aes_nonce_t)
  (counter_276 : uint32)
  (ctxt_277 : byte_seq)
  : byte_seq :=
  result_unwrap (aes_counter_mode (seq_from_seq (array_to_seq (key_274))) (
      nonce_275) (counter_276) (ctxt_277) (key_length_v) (rounds_v) (
      key_schedule_length_v) (key_length_v) (iterations_v)).


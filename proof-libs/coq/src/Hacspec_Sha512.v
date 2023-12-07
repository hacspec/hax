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
  usize 128.

Definition len_size_v : uint_size :=
  usize 16.

Definition k_size_v : uint_size :=
  usize 80.

Definition hash_size_v : uint_size :=
  (usize 512) / (usize 8).

Definition block_t := nseq (uint8) (block_size_v).

Definition op_table_type_t := nseq (uint_size) (usize 12).

Definition sha512_digest_t := nseq (uint8) (hash_size_v).

Definition round_constants_table_t := nseq (uint64) (k_size_v).

Definition hash_t := nseq (uint64) (usize 8).

Definition ch (x_2240 : uint64) (y_2241 : uint64) (z_2242 : uint64) : uint64 :=
  ((x_2240) .& (y_2241)) .^ ((not (x_2240)) .& (z_2242)).

Definition maj (x_2243 : uint64) (y_2244 : uint64) (z_2245 : uint64) : uint64 :=
  ((x_2243) .& (y_2244)) .^ (((x_2243) .& (z_2245)) .^ ((y_2244) .& (z_2245))).

Definition op_table_v : op_table_type_t :=
  array_from_list uint_size (let l :=
      [
        usize 28;
        usize 34;
        usize 39;
        usize 14;
        usize 18;
        usize 41;
        usize 1;
        usize 8;
        usize 7;
        usize 19;
        usize 61;
        usize 6
      ] in  l).

Definition k_table_v : round_constants_table_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 4794697086780616226) : int64;
        secret (@repr WORDSIZE64 8158064640168781261) : int64;
        secret (@repr WORDSIZE64 13096744586834688815) : int64;
        secret (@repr WORDSIZE64 16840607885511220156) : int64;
        secret (@repr WORDSIZE64 4131703408338449720) : int64;
        secret (@repr WORDSIZE64 6480981068601479193) : int64;
        secret (@repr WORDSIZE64 10538285296894168987) : int64;
        secret (@repr WORDSIZE64 12329834152419229976) : int64;
        secret (@repr WORDSIZE64 15566598209576043074) : int64;
        secret (@repr WORDSIZE64 1334009975649890238) : int64;
        secret (@repr WORDSIZE64 2608012711638119052) : int64;
        secret (@repr WORDSIZE64 6128411473006802146) : int64;
        secret (@repr WORDSIZE64 8268148722764581231) : int64;
        secret (@repr WORDSIZE64 9286055187155687089) : int64;
        secret (@repr WORDSIZE64 11230858885718282805) : int64;
        secret (@repr WORDSIZE64 13951009754708518548) : int64;
        secret (@repr WORDSIZE64 16472876342353939154) : int64;
        secret (@repr WORDSIZE64 17275323862435702243) : int64;
        secret (@repr WORDSIZE64 1135362057144423861) : int64;
        secret (@repr WORDSIZE64 2597628984639134821) : int64;
        secret (@repr WORDSIZE64 3308224258029322869) : int64;
        secret (@repr WORDSIZE64 5365058923640841347) : int64;
        secret (@repr WORDSIZE64 6679025012923562964) : int64;
        secret (@repr WORDSIZE64 8573033837759648693) : int64;
        secret (@repr WORDSIZE64 10970295158949994411) : int64;
        secret (@repr WORDSIZE64 12119686244451234320) : int64;
        secret (@repr WORDSIZE64 12683024718118986047) : int64;
        secret (@repr WORDSIZE64 13788192230050041572) : int64;
        secret (@repr WORDSIZE64 14330467153632333762) : int64;
        secret (@repr WORDSIZE64 15395433587784984357) : int64;
        secret (@repr WORDSIZE64 489312712824947311) : int64;
        secret (@repr WORDSIZE64 1452737877330783856) : int64;
        secret (@repr WORDSIZE64 2861767655752347644) : int64;
        secret (@repr WORDSIZE64 3322285676063803686) : int64;
        secret (@repr WORDSIZE64 5560940570517711597) : int64;
        secret (@repr WORDSIZE64 5996557281743188959) : int64;
        secret (@repr WORDSIZE64 7280758554555802590) : int64;
        secret (@repr WORDSIZE64 8532644243296465576) : int64;
        secret (@repr WORDSIZE64 9350256976987008742) : int64;
        secret (@repr WORDSIZE64 10552545826968843579) : int64;
        secret (@repr WORDSIZE64 11727347734174303076) : int64;
        secret (@repr WORDSIZE64 12113106623233404929) : int64;
        secret (@repr WORDSIZE64 14000437183269869457) : int64;
        secret (@repr WORDSIZE64 14369950271660146224) : int64;
        secret (@repr WORDSIZE64 15101387698204529176) : int64;
        secret (@repr WORDSIZE64 15463397548674623760) : int64;
        secret (@repr WORDSIZE64 17586052441742319658) : int64;
        secret (@repr WORDSIZE64 1182934255886127544) : int64;
        secret (@repr WORDSIZE64 1847814050463011016) : int64;
        secret (@repr WORDSIZE64 2177327727835720531) : int64;
        secret (@repr WORDSIZE64 2830643537854262169) : int64;
        secret (@repr WORDSIZE64 3796741975233480872) : int64;
        secret (@repr WORDSIZE64 4115178125766777443) : int64;
        secret (@repr WORDSIZE64 5681478168544905931) : int64;
        secret (@repr WORDSIZE64 6601373596472566643) : int64;
        secret (@repr WORDSIZE64 7507060721942968483) : int64;
        secret (@repr WORDSIZE64 8399075790359081724) : int64;
        secret (@repr WORDSIZE64 8693463985226723168) : int64;
        secret (@repr WORDSIZE64 9568029438360202098) : int64;
        secret (@repr WORDSIZE64 10144078919501101548) : int64;
        secret (@repr WORDSIZE64 10430055236837252648) : int64;
        secret (@repr WORDSIZE64 11840083180663258601) : int64;
        secret (@repr WORDSIZE64 13761210420658862357) : int64;
        secret (@repr WORDSIZE64 14299343276471374635) : int64;
        secret (@repr WORDSIZE64 14566680578165727644) : int64;
        secret (@repr WORDSIZE64 15097957966210449927) : int64;
        secret (@repr WORDSIZE64 16922976911328602910) : int64;
        secret (@repr WORDSIZE64 17689382322260857208) : int64;
        secret (@repr WORDSIZE64 500013540394364858) : int64;
        secret (@repr WORDSIZE64 748580250866718886) : int64;
        secret (@repr WORDSIZE64 1242879168328830382) : int64;
        secret (@repr WORDSIZE64 1977374033974150939) : int64;
        secret (@repr WORDSIZE64 2944078676154940804) : int64;
        secret (@repr WORDSIZE64 3659926193048069267) : int64;
        secret (@repr WORDSIZE64 4368137639120453308) : int64;
        secret (@repr WORDSIZE64 4836135668995329356) : int64;
        secret (@repr WORDSIZE64 5532061633213252278) : int64;
        secret (@repr WORDSIZE64 6448918945643986474) : int64;
        secret (@repr WORDSIZE64 6902733635092675308) : int64;
        secret (@repr WORDSIZE64 7801388544844847127) : int64
      ] in  l).

Definition hash_init_v : hash_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 7640891576956012808) : int64;
        secret (@repr WORDSIZE64 13503953896175478587) : int64;
        secret (@repr WORDSIZE64 4354685564936845355) : int64;
        secret (@repr WORDSIZE64 11912009170470909681) : int64;
        secret (@repr WORDSIZE64 5840696475078001361) : int64;
        secret (@repr WORDSIZE64 11170449401992604703) : int64;
        secret (@repr WORDSIZE64 2270897969802886507) : int64;
        secret (@repr WORDSIZE64 6620516959819538809) : int64
      ] in  l).

Definition sigma
  (x_2246 : uint64)
  (i_2247 : uint_size)
  (op_2248 : uint_size)
  : uint64 :=
  let tmp_2249 : uint64 :=
    uint64_rotate_right (x_2246) (array_index (op_table_v) (((usize 3) * (
            i_2247)) + (usize 2))) in 
  let '(tmp_2249) :=
    if (op_2248) =.? (usize 0):bool then (let tmp_2249 :=
        (x_2246) shift_right (array_index (op_table_v) (((usize 3) * (
                i_2247)) + (usize 2))) in 
      (tmp_2249)) else ((tmp_2249)) in 
  ((uint64_rotate_right (x_2246) (array_index (op_table_v) ((usize 3) * (
            i_2247)))) .^ (uint64_rotate_right (x_2246) (array_index (
          op_table_v) (((usize 3) * (i_2247)) + (usize 1))))) .^ (tmp_2249).

Definition schedule (block_2250 : block_t) : round_constants_table_t :=
  let b_2251 : seq uint64 :=
    array_to_be_uint64s (block_2250) in 
  let s_2252 : round_constants_table_t :=
    array_new_ (default : uint64) (k_size_v) in 
  let s_2252 :=
    foldi (usize 0) (k_size_v) (fun i_2253 s_2252 =>
      let '(s_2252) :=
        if (i_2253) <.? (usize 16):bool then (let s_2252 :=
            array_upd s_2252 (i_2253) (seq_index (b_2251) (i_2253)) in 
          (s_2252)) else (let t16_2254 : uint64 :=
            array_index (s_2252) ((i_2253) - (usize 16)) in 
          let t15_2255 : uint64 :=
            array_index (s_2252) ((i_2253) - (usize 15)) in 
          let t7_2256 : uint64 :=
            array_index (s_2252) ((i_2253) - (usize 7)) in 
          let t2_2257 : uint64 :=
            array_index (s_2252) ((i_2253) - (usize 2)) in 
          let s1_2258 : uint64 :=
            sigma (t2_2257) (usize 3) (usize 0) in 
          let s0_2259 : uint64 :=
            sigma (t15_2255) (usize 2) (usize 0) in 
          let s_2252 :=
            array_upd s_2252 (i_2253) ((((s1_2258) .+ (t7_2256)) .+ (
                  s0_2259)) .+ (t16_2254)) in 
          (s_2252)) in 
      (s_2252))
    s_2252 in 
  s_2252.

Definition shuffle
  (ws_2260 : round_constants_table_t)
  (hashi_2261 : hash_t)
  : hash_t :=
  let h_2262 : hash_t :=
    hashi_2261 in 
  let h_2262 :=
    foldi (usize 0) (k_size_v) (fun i_2263 h_2262 =>
      let a0_2264 : uint64 :=
        array_index (h_2262) (usize 0) in 
      let b0_2265 : uint64 :=
        array_index (h_2262) (usize 1) in 
      let c0_2266 : uint64 :=
        array_index (h_2262) (usize 2) in 
      let d0_2267 : uint64 :=
        array_index (h_2262) (usize 3) in 
      let e0_2268 : uint64 :=
        array_index (h_2262) (usize 4) in 
      let f0_2269 : uint64 :=
        array_index (h_2262) (usize 5) in 
      let g0_2270 : uint64 :=
        array_index (h_2262) (usize 6) in 
      let h0_2271 : uint64 :=
        array_index (h_2262) (usize 7) in 
      let t1_2272 : uint64 :=
        ((((h0_2271) .+ (sigma (e0_2268) (usize 1) (usize 1))) .+ (ch (
                e0_2268) (f0_2269) (g0_2270))) .+ (array_index (k_table_v) (
              i_2263))) .+ (array_index (ws_2260) (i_2263)) in 
      let t2_2273 : uint64 :=
        (sigma (a0_2264) (usize 0) (usize 1)) .+ (maj (a0_2264) (b0_2265) (
            c0_2266)) in 
      let h_2262 :=
        array_upd h_2262 (usize 0) ((t1_2272) .+ (t2_2273)) in 
      let h_2262 :=
        array_upd h_2262 (usize 1) (a0_2264) in 
      let h_2262 :=
        array_upd h_2262 (usize 2) (b0_2265) in 
      let h_2262 :=
        array_upd h_2262 (usize 3) (c0_2266) in 
      let h_2262 :=
        array_upd h_2262 (usize 4) ((d0_2267) .+ (t1_2272)) in 
      let h_2262 :=
        array_upd h_2262 (usize 5) (e0_2268) in 
      let h_2262 :=
        array_upd h_2262 (usize 6) (f0_2269) in 
      let h_2262 :=
        array_upd h_2262 (usize 7) (g0_2270) in 
      (h_2262))
    h_2262 in 
  h_2262.

Definition compress (block_2274 : block_t) (h_in_2275 : hash_t) : hash_t :=
  let s_2276 : round_constants_table_t :=
    schedule (block_2274) in 
  let h_2277 : hash_t :=
    shuffle (s_2276) (h_in_2275) in 
  let h_2277 :=
    foldi (usize 0) (usize 8) (fun i_2278 h_2277 =>
      let h_2277 :=
        array_upd h_2277 (i_2278) ((array_index (h_2277) (i_2278)) .+ (
            array_index (h_in_2275) (i_2278))) in 
      (h_2277))
    h_2277 in 
  h_2277.

Definition hash (msg_2279 : byte_seq) : sha512_digest_t :=
  let h_2280 : hash_t :=
    hash_init_v in 
  let last_block_2281 : block_t :=
    array_new_ (default : uint8) (block_size_v) in 
  let last_block_len_2282 : uint_size :=
    usize 0 in 
  let '(h_2280, last_block_2281, last_block_len_2282) :=
    foldi (usize 0) (seq_num_chunks (msg_2279) (block_size_v)) (fun i_2283 '(
        h_2280,
        last_block_2281,
        last_block_len_2282
      ) =>
      let '(block_len_2284, block_2285) :=
        seq_get_chunk (msg_2279) (block_size_v) (i_2283) in 
      let '(h_2280, last_block_2281, last_block_len_2282) :=
        if (block_len_2284) <.? (block_size_v):bool then (let last_block_2281 :=
            array_update_start (array_new_ (default : uint8) (block_size_v)) (
              block_2285) in 
          let last_block_len_2282 :=
            block_len_2284 in 
          (h_2280, last_block_2281, last_block_len_2282)) else (
          let compress_input_2286 : block_t :=
            array_from_seq (block_size_v) (block_2285) in 
          let h_2280 :=
            compress (compress_input_2286) (h_2280) in 
          (h_2280, last_block_2281, last_block_len_2282)) in 
      (h_2280, last_block_2281, last_block_len_2282))
    (h_2280, last_block_2281, last_block_len_2282) in 
  let last_block_2281 :=
    array_upd last_block_2281 (last_block_len_2282) (secret (
        @repr WORDSIZE8 128) : int8) in 
  let len_bist_2287 : uint128 :=
    secret (pub_u128 ((seq_len (msg_2279)) * (usize 8))) : int128 in 
  let '(h_2280, last_block_2281) :=
    if (last_block_len_2282) <.? ((block_size_v) - (len_size_v)):bool then (
      let last_block_2281 :=
        array_update (last_block_2281) ((block_size_v) - (len_size_v)) (
          array_to_seq (uint128_to_be_bytes (len_bist_2287))) in 
      let h_2280 :=
        compress (last_block_2281) (h_2280) in 
      (h_2280, last_block_2281)) else (let pad_block_2288 : block_t :=
        array_new_ (default : uint8) (block_size_v) in 
      let pad_block_2288 :=
        array_update (pad_block_2288) ((block_size_v) - (len_size_v)) (
          array_to_seq (uint128_to_be_bytes (len_bist_2287))) in 
      let h_2280 :=
        compress (last_block_2281) (h_2280) in 
      let h_2280 :=
        compress (pad_block_2288) (h_2280) in 
      (h_2280, last_block_2281)) in 
  array_from_seq (hash_size_v) (array_to_be_bytes (h_2280)).

Definition sha512 (msg_2289 : byte_seq) : sha512_digest_t :=
  hash (msg_2289).


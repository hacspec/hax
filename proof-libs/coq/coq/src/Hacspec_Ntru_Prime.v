(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition build_irreducible (p_1256 : uint_size) : seq int128 :=
  let irr_1257 : seq int128 :=
    seq_new_ (default : int128) ((p_1256) + (usize 1)) in 
  let irr_1257 :=
    seq_upd irr_1257 (usize 0) (- (@repr WORDSIZE128 1)) in 
  let irr_1257 :=
    seq_upd irr_1257 (usize 1) (- (@repr WORDSIZE128 1)) in 
  let irr_1257 :=
    seq_upd irr_1257 (p_1256) (@repr WORDSIZE128 1) in 
  irr_1257.

Definition round_to_3 (poly_1258 : seq int128) (q_1259 : int128) : seq int128 :=
  let result_1260 : seq int128 :=
    (poly_1258) in 
  let q_12_1261 : int128 :=
    ((q_1259) .- (@repr WORDSIZE128 1)) ./ (@repr WORDSIZE128 2) in 
  let result_1260 :=
    foldi (usize 0) (seq_len (poly_1258)) (fun i_1262 result_1260 =>
      let '(result_1260) :=
        if (seq_index (poly_1258) (i_1262)) >.? (q_12_1261):bool then (
          let result_1260 :=
            seq_upd result_1260 (i_1262) ((seq_index (poly_1258) (i_1262)) .- (
                q_1259)) in 
          (result_1260)) else ((result_1260)) in 
      (result_1260))
    result_1260 in 
  let result_1260 :=
    foldi (usize 0) (seq_len (result_1260)) (fun i_1263 result_1260 =>
      let '(result_1260) :=
        if ((seq_index (result_1260) (i_1263)) .% (@repr WORDSIZE128 3)) !=.? (
          @repr WORDSIZE128 0):bool then (let result_1260 :=
            seq_upd result_1260 (i_1263) ((seq_index (result_1260) (
                  i_1263)) .- (@repr WORDSIZE128 1)) in 
          let '(result_1260) :=
            if ((seq_index (result_1260) (i_1263)) .% (
                @repr WORDSIZE128 3)) !=.? (@repr WORDSIZE128 0):bool then (
              let result_1260 :=
                seq_upd result_1260 (i_1263) ((seq_index (result_1260) (
                      i_1263)) .+ (@repr WORDSIZE128 2)) in 
              (result_1260)) else ((result_1260)) in 
          (result_1260)) else ((result_1260)) in 
      (result_1260))
    result_1260 in 
  result_1260.

Definition encrypt
  (r_1264 : seq int128)
  (h_1265 : seq int128)
  (q_1266 : int128)
  (irreducible_1267 : seq int128)
  : seq int128 :=
  let pre_1268 : seq int128 :=
    mul_poly_irr (r_1264) (h_1265) (irreducible_1267) (q_1266) in 
  round_to_3 (pre_1268) (q_1266).

Definition ntru_prime_653_encrypt
  (r_1269 : seq int128)
  (h_1270 : seq int128)
  : seq int128 :=
  let p_1271 : uint_size :=
    usize 653 in 
  let q_1272 : int128 :=
    @repr WORDSIZE128 4621 in 
  let w_1273 : uint_size :=
    usize 288 in 
  let irreducible_1274 : seq int128 :=
    build_irreducible (p_1271) in 
  encrypt (r_1269) (h_1270) (q_1272) (irreducible_1274).

Definition ntru_prime_653_decrypt
  (c_1275 : seq int128)
  (key_f_1276 : seq int128)
  (key_v_1277 : seq int128)
  : (seq int128 '× bool) :=
  let p_1278 : uint_size :=
    usize 653 in 
  let q_1279 : int128 :=
    @repr WORDSIZE128 4621 in 
  let w_1280 : uint_size :=
    usize 288 in 
  let irreducible_1281 : seq int128 :=
    build_irreducible (p_1278) in 
  let f_c_1282 : seq int128 :=
    mul_poly_irr (key_f_1276) (c_1275) (irreducible_1281) (q_1279) in 
  let f_3_c_and_decryption_ok_1283 : (seq int128 '× bool) :=
    poly_to_ring (irreducible_1281) (add_poly (f_c_1282) (add_poly (f_c_1282) (
          f_c_1282) (q_1279)) (q_1279)) (q_1279) in 
  let '(f_3_c_1284, ok_decrypt_1285) :=
    f_3_c_and_decryption_ok_1283 in 
  let f_3_c_1286 : seq int128 :=
    f_3_c_1284 in 
  let q_12_1287 : int128 :=
    ((q_1279) .- (@repr WORDSIZE128 1)) ./ (@repr WORDSIZE128 2) in 
  let f_3_c_1286 :=
    foldi (usize 0) (seq_len (f_3_c_1286)) (fun i_1288 f_3_c_1286 =>
      let '(f_3_c_1286) :=
        if (seq_index (f_3_c_1286) (i_1288)) >.? (q_12_1287):bool then (
          let f_3_c_1286 :=
            seq_upd f_3_c_1286 (i_1288) ((seq_index (f_3_c_1286) (i_1288)) .- (
                q_1279)) in 
          (f_3_c_1286)) else ((f_3_c_1286)) in 
      (f_3_c_1286))
    f_3_c_1286 in 
  let e_1289 : seq int128 :=
    seq_new_ (default : int128) (seq_len (f_3_c_1286)) in 
  let e_1289 :=
    foldi (usize 0) (seq_len (e_1289)) (fun i_1290 e_1289 =>
      let e_1289 :=
        seq_upd e_1289 (i_1290) ((seq_index (f_3_c_1286) (i_1290)) .% (
            @repr WORDSIZE128 3)) in 
      (e_1289))
    e_1289 in 
  let e_1289 :=
    make_positive (e_1289) (@repr WORDSIZE128 3) in 
  let r_1291 : seq int128 :=
    mul_poly_irr (e_1289) (key_v_1277) (irreducible_1281) (
      @repr WORDSIZE128 3) in 
  let r_1291 :=
    foldi (usize 0) (seq_len (r_1291)) (fun i_1292 r_1291 =>
      let '(r_1291) :=
        if (seq_index (r_1291) (i_1292)) =.? (@repr WORDSIZE128 2):bool then (
          let r_1291 :=
            seq_upd r_1291 (i_1292) (- (@repr WORDSIZE128 1)) in 
          (r_1291)) else ((r_1291)) in 
      (r_1291))
    r_1291 in 
  (r_1291, ok_decrypt_1285).


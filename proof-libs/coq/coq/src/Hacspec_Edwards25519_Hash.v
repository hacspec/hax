(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_Edwards25519.

Require Import Hacspec_Sha512.

Definition b_in_bytes_v : uint_size :=
  usize 64.

Definition s_in_bytes_v : uint_size :=
  usize 128.

Definition l_v : uint_size :=
  usize 48.

Definition j_v : int128 :=
  @repr WORDSIZE128 486662.

Definition z_v : int128 :=
  @repr WORDSIZE128 2.

Definition arr_ed25519_field_element_t := nseq (uint64) (usize 4).

Definition ed_field_hash_canvas_t := nseq (int8) (64).
Definition ed_field_hash_t :=
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Inductive error_t :=
| ExpandMessageAbort : error_t.

Definition eqb_error_t (x y : error_t) : bool :=
match x with
   | ExpandMessageAbort => match y with | ExpandMessageAbort=> true end
   end.

Definition eqb_leibniz_error_t (x y : error_t) : eqb_error_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_error_t : EqDec (error_t) :=
Build_EqDec (error_t) (eqb_error_t) (eqb_leibniz_error_t).


Notation "'byte_seq_result_t'" := ((result byte_seq error_t)) : hacspec_scope.

Notation "'seq_ed_result_t'" := ((
  result seq ed25519_field_element_t error_t)) : hacspec_scope.

Notation "'ed_point_result_t'" := ((result ed_point_t error_t)) : hacspec_scope.

Definition p_1_2_v : arr_ed25519_field_element_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 4611686018427387903) : int64;
        secret (@repr WORDSIZE64 18446744073709551615) : int64;
        secret (@repr WORDSIZE64 18446744073709551615) : int64;
        secret (@repr WORDSIZE64 18446744073709551606) : int64
      ] in  l).

Definition p_3_8_v : arr_ed25519_field_element_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1152921504606846975) : int64;
        secret (@repr WORDSIZE64 18446744073709551615) : int64;
        secret (@repr WORDSIZE64 18446744073709551615) : int64;
        secret (@repr WORDSIZE64 18446744073709551614) : int64
      ] in  l).

Definition p_5_8_v : arr_ed25519_field_element_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1152921504606846975) : int64;
        secret (@repr WORDSIZE64 18446744073709551615) : int64;
        secret (@repr WORDSIZE64 18446744073709551615) : int64;
        secret (@repr WORDSIZE64 18446744073709551613) : int64
      ] in  l).

Definition expand_message_xmd
  (msg_2290 : byte_seq)
  (dst_2291 : byte_seq)
  (len_in_bytes_2292 : uint_size)
  : byte_seq_result_t :=
  let ell_2293 : uint_size :=
    (((len_in_bytes_2292) + (b_in_bytes_v)) - (usize 1)) / (b_in_bytes_v) in 
  let result_2294 : (result byte_seq error_t) :=
    @Err byte_seq error_t (ExpandMessageAbort) in 
  let '(result_2294) :=
    if negb ((((ell_2293) >.? (usize 255)) || ((len_in_bytes_2292) >.? (
            usize 65535))) || ((seq_len (dst_2291)) >.? (
          usize 255))):bool then (let dst_prime_2295 : seq uint8 :=
        seq_push (dst_2291) (uint8_from_usize (seq_len (dst_2291))) in 
      let z_pad_2296 : seq uint8 :=
        seq_new_ (default : uint8) (s_in_bytes_v) in 
      let l_i_b_str_2297 : seq uint8 :=
        seq_new_ (default : uint8) (usize 2) in 
      let l_i_b_str_2297 :=
        seq_upd l_i_b_str_2297 (usize 0) (uint8_from_usize ((
              len_in_bytes_2292) / (usize 256))) in 
      let l_i_b_str_2297 :=
        seq_upd l_i_b_str_2297 (usize 1) (uint8_from_usize (
            len_in_bytes_2292)) in 
      let msg_prime_2298 : seq uint8 :=
        seq_concat (seq_concat (seq_concat (seq_concat (z_pad_2296) (
                msg_2290)) (l_i_b_str_2297)) (seq_new_ (default : uint8) (
              usize 1))) (dst_prime_2295) in 
      let b_0_2299 : seq uint8 :=
        seq_from_seq (array_to_seq (hash (msg_prime_2298))) in 
      let b_i_2300 : seq uint8 :=
        seq_from_seq (array_to_seq (hash (seq_concat (seq_push (b_0_2299) (
                secret (@repr WORDSIZE8 1) : int8)) (dst_prime_2295)))) in 
      let uniform_bytes_2301 : seq uint8 :=
        seq_from_seq (b_i_2300) in 
      let '(b_i_2300, uniform_bytes_2301) :=
        foldi (usize 2) ((ell_2293) + (usize 1)) (fun i_2302 '(
            b_i_2300,
            uniform_bytes_2301
          ) =>
          let t_2303 : seq uint8 :=
            seq_from_seq (b_0_2299) in 
          let b_i_2300 :=
            seq_from_seq (array_to_seq (hash (seq_concat (seq_push ((
                      t_2303) seq_xor (b_i_2300)) (uint8_from_usize (i_2302))) (
                  dst_prime_2295)))) in 
          let uniform_bytes_2301 :=
            seq_concat (uniform_bytes_2301) (b_i_2300) in 
          (b_i_2300, uniform_bytes_2301))
        (b_i_2300, uniform_bytes_2301) in 
      let result_2294 :=
        @Ok byte_seq error_t (seq_truncate (uniform_bytes_2301) (
            len_in_bytes_2292)) in 
      (result_2294)) else ((result_2294)) in 
  result_2294.

Definition ed_hash_to_field
  (msg_2304 : byte_seq)
  (dst_2305 : byte_seq)
  (count_2306 : uint_size)
  : seq_ed_result_t :=
  let len_in_bytes_2307 : uint_size :=
    (count_2306) * (l_v) in 
  bind (expand_message_xmd (msg_2304) (dst_2305) (len_in_bytes_2307)) (
    fun uniform_bytes_2308 => let output_2309 : seq ed25519_field_element_t :=
      seq_new_ (default : ed25519_field_element_t) (count_2306) in 
    let output_2309 :=
      foldi (usize 0) (count_2306) (fun i_2310 output_2309 =>
        let elm_offset_2311 : uint_size :=
          (l_v) * (i_2310) in 
        let tv_2312 : seq uint8 :=
          seq_slice (uniform_bytes_2308) (elm_offset_2311) (l_v) in 
        let u_i_2313 : ed25519_field_element_t :=
          nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
                nat_mod_from_byte_seq_be (tv_2312) : ed_field_hash_t)) (
              usize 32) (usize 32)) : ed25519_field_element_t in 
        let output_2309 :=
          seq_upd output_2309 (i_2310) (u_i_2313) in 
        (output_2309))
      output_2309 in 
    @Ok seq ed25519_field_element_t error_t (output_2309)).

Definition ed_is_square (x_2314 : ed25519_field_element_t) : bool :=
  let c1_2315 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (
        p_1_2_v)) : ed25519_field_element_t in 
  let tv_2316 : ed25519_field_element_t :=
    nat_mod_pow_self (x_2314) (c1_2315) in 
  ((tv_2316) =.? (nat_mod_zero )) || ((tv_2316) =.? (nat_mod_one )).

Definition sgn0_m_eq_1 (x_2317 : ed25519_field_element_t) : bool :=
  ((x_2317) rem (nat_mod_two )) =.? (nat_mod_one ).

Definition ed_clear_cofactor (x_2318 : ed_point_t) : ed_point_t :=
  point_mul_by_cofactor (x_2318).

Definition cmov
  (a_2319 : ed25519_field_element_t)
  (b_2320 : ed25519_field_element_t)
  (c_2321 : bool)
  : ed25519_field_element_t :=
  (if (c_2321):bool then (b_2320) else (a_2319)).

Definition xor (a_2322 : bool) (b_2323 : bool) : bool :=
  (if (a_2322):bool then ((if (b_2323):bool then (false) else (true))) else ((
        if (b_2323):bool then (true) else (false)))).

Definition curve25519_to_edwards25519 (p_2324 : ed_point_t) : ed_point_t :=
  let '(s_2325, t_2326, _, _) :=
    point_normalize (p_2324) in 
  let one_2327 : ed25519_field_element_t :=
    nat_mod_one  in 
  let zero_2328 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let tv1_2329 : ed25519_field_element_t :=
    (s_2325) +% (one_2327) in 
  let tv2_2330 : ed25519_field_element_t :=
    (tv1_2329) *% (t_2326) in 
  let tv2_2331 : ed25519_field_element_t :=
    nat_mod_inv (tv2_2330) in 
  let v_2332 : ed25519_field_element_t :=
    (tv2_2331) *% (tv1_2329) in 
  let v_2333 : ed25519_field_element_t :=
    (v_2332) *% (s_2325) in 
  let w_2334 : ed25519_field_element_t :=
    (tv2_2331) *% (t_2326) in 
  let tv1_2335 : ed25519_field_element_t :=
    (s_2325) -% (one_2327) in 
  let w_2336 : ed25519_field_element_t :=
    (w_2334) *% (tv1_2335) in 
  let e_2337 : bool :=
    (tv2_2331) =.? (zero_2328) in 
  let w_2338 : ed25519_field_element_t :=
    cmov (w_2336) (one_2327) (e_2337) in 
  let c_2339 : ed25519_field_element_t :=
    (nat_mod_zero ) -% (nat_mod_from_literal (_) (
        @repr WORDSIZE128 486664) : ed25519_field_element_t) in 
  let sq_2340 : (option ed25519_field_element_t) :=
    sqrt (c_2339) in 
  let v_2341 : ed25519_field_element_t :=
    (v_2333) *% (option_unwrap (sq_2340)) in 
  (v_2341, w_2338, one_2327, (v_2341) *% (w_2338)).

Definition map_to_curve_elligator2
  (u_2342 : ed25519_field_element_t)
  : ed_point_t :=
  let j_2343 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (j_v) : ed25519_field_element_t in 
  let z_2344 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (z_v) : ed25519_field_element_t in 
  let one_2345 : ed25519_field_element_t :=
    nat_mod_one  in 
  let zero_2346 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let x1_2347 : ed25519_field_element_t :=
    ((zero_2346) -% (j_2343)) *% (nat_mod_inv ((one_2345) +% (((z_2344) *% (
              u_2342)) *% (u_2342)))) in 
  let '(x1_2347) :=
    if (x1_2347) =.? (zero_2346):bool then (let x1_2347 :=
        (zero_2346) -% (j_2343) in 
      (x1_2347)) else ((x1_2347)) in 
  let gx1_2348 : ed25519_field_element_t :=
    ((((x1_2347) *% (x1_2347)) *% (x1_2347)) +% (((j_2343) *% (x1_2347)) *% (
          x1_2347))) +% (x1_2347) in 
  let x2_2349 : ed25519_field_element_t :=
    ((zero_2346) -% (x1_2347)) -% (j_2343) in 
  let gx2_2350 : ed25519_field_element_t :=
    ((((x2_2349) *% (x2_2349)) *% (x2_2349)) +% ((j_2343) *% ((x2_2349) *% (
            x2_2349)))) +% (x2_2349) in 
  let x_2351 : ed25519_field_element_t :=
    zero_2346 in 
  let y_2352 : ed25519_field_element_t :=
    zero_2346 in 
  let '(x_2351, y_2352) :=
    if ed_is_square (gx1_2348):bool then (let x_2351 :=
        x1_2347 in 
      let y_2352 :=
        option_unwrap (sqrt (gx1_2348)) in 
      let '(y_2352) :=
        if negb (sgn0_m_eq_1 (y_2352)):bool then (let y_2352 :=
            (zero_2346) -% (y_2352) in 
          (y_2352)) else ((y_2352)) in 
      (x_2351, y_2352)) else (let x_2351 :=
        x2_2349 in 
      let y_2352 :=
        option_unwrap (sqrt (gx2_2350)) in 
      let '(y_2352) :=
        if sgn0_m_eq_1 (y_2352):bool then (let y_2352 :=
            (zero_2346) -% (y_2352) in 
          (y_2352)) else ((y_2352)) in 
      (x_2351, y_2352)) in 
  let s_2353 : ed25519_field_element_t :=
    x_2351 in 
  let t_2354 : ed25519_field_element_t :=
    y_2352 in 
  (s_2353, t_2354, one_2345, (s_2353) *% (t_2354)).

Definition map_to_curve_elligator2_straight
  (u_2355 : ed25519_field_element_t)
  : ed_point_t :=
  let j_2356 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (j_v) : ed25519_field_element_t in 
  let z_2357 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (z_v) : ed25519_field_element_t in 
  let one_2358 : ed25519_field_element_t :=
    nat_mod_one  in 
  let zero_2359 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let tv1_2360 : ed25519_field_element_t :=
    (u_2355) *% (u_2355) in 
  let tv1_2361 : ed25519_field_element_t :=
    (z_2357) *% (tv1_2360) in 
  let e1_2362 : bool :=
    (tv1_2361) =.? ((zero_2359) -% (one_2358)) in 
  let tv1_2363 : ed25519_field_element_t :=
    cmov (tv1_2361) (zero_2359) (e1_2362) in 
  let x1_2364 : ed25519_field_element_t :=
    (tv1_2363) +% (one_2358) in 
  let x1_2365 : ed25519_field_element_t :=
    nat_mod_inv (x1_2364) in 
  let x1_2366 : ed25519_field_element_t :=
    ((zero_2359) -% (j_2356)) *% (x1_2365) in 
  let gx1_2367 : ed25519_field_element_t :=
    (x1_2366) +% (j_2356) in 
  let gx1_2368 : ed25519_field_element_t :=
    (gx1_2367) *% (x1_2366) in 
  let gx1_2369 : ed25519_field_element_t :=
    (gx1_2368) +% (one_2358) in 
  let gx1_2370 : ed25519_field_element_t :=
    (gx1_2369) *% (x1_2366) in 
  let x2_2371 : ed25519_field_element_t :=
    ((zero_2359) -% (x1_2366)) -% (j_2356) in 
  let gx2_2372 : ed25519_field_element_t :=
    (tv1_2363) *% (gx1_2370) in 
  let e2_2373 : bool :=
    ed_is_square (gx1_2370) in 
  let x_2374 : ed25519_field_element_t :=
    cmov (x2_2371) (x1_2366) (e2_2373) in 
  let y2_2375 : ed25519_field_element_t :=
    cmov (gx2_2372) (gx1_2370) (e2_2373) in 
  let y_2376 : ed25519_field_element_t :=
    option_unwrap (sqrt (y2_2375)) in 
  let e3_2377 : bool :=
    sgn0_m_eq_1 (y_2376) in 
  let y_2378 : ed25519_field_element_t :=
    cmov (y_2376) ((zero_2359) -% (y_2376)) (xor (e2_2373) (e3_2377)) in 
  let s_2379 : ed25519_field_element_t :=
    x_2374 in 
  let t_2380 : ed25519_field_element_t :=
    y_2378 in 
  (s_2379, t_2380, one_2358, (s_2379) *% (t_2380)).

Definition map_to_curve_elligator2_curve25519
  (u_2381 : ed25519_field_element_t)
  : ed_point_t :=
  let j_2382 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (j_v) : ed25519_field_element_t in 
  let zero_2383 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let one_2384 : ed25519_field_element_t :=
    nat_mod_one  in 
  let two_2385 : ed25519_field_element_t :=
    nat_mod_two  in 
  let c1_2386 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (
        p_3_8_v)) : ed25519_field_element_t in 
  let c2_2387 : ed25519_field_element_t :=
    nat_mod_pow_self (two_2385) (c1_2386) in 
  let c3_2388 : ed25519_field_element_t :=
    option_unwrap (sqrt ((zero_2383) -% (one_2384))) in 
  let c4_2389 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (
        p_5_8_v)) : ed25519_field_element_t in 
  let tv1_2390 : ed25519_field_element_t :=
    (u_2381) *% (u_2381) in 
  let tv1_2391 : ed25519_field_element_t :=
    (two_2385) *% (tv1_2390) in 
  let xd_2392 : ed25519_field_element_t :=
    (tv1_2391) +% (one_2384) in 
  let x1n_2393 : ed25519_field_element_t :=
    (zero_2383) -% (j_2382) in 
  let tv2_2394 : ed25519_field_element_t :=
    (xd_2392) *% (xd_2392) in 
  let gxd_2395 : ed25519_field_element_t :=
    (tv2_2394) *% (xd_2392) in 
  let gx1_2396 : ed25519_field_element_t :=
    (j_2382) *% (tv1_2391) in 
  let gx1_2397 : ed25519_field_element_t :=
    (gx1_2396) *% (x1n_2393) in 
  let gx1_2398 : ed25519_field_element_t :=
    (gx1_2397) +% (tv2_2394) in 
  let gx1_2399 : ed25519_field_element_t :=
    (gx1_2398) *% (x1n_2393) in 
  let tv3_2400 : ed25519_field_element_t :=
    (gxd_2395) *% (gxd_2395) in 
  let tv2_2401 : ed25519_field_element_t :=
    (tv3_2400) *% (tv3_2400) in 
  let tv3_2402 : ed25519_field_element_t :=
    (tv3_2400) *% (gxd_2395) in 
  let tv3_2403 : ed25519_field_element_t :=
    (tv3_2402) *% (gx1_2399) in 
  let tv2_2404 : ed25519_field_element_t :=
    (tv2_2401) *% (tv3_2403) in 
  let y11_2405 : ed25519_field_element_t :=
    nat_mod_pow_self (tv2_2404) (c4_2389) in 
  let y11_2406 : ed25519_field_element_t :=
    (y11_2405) *% (tv3_2403) in 
  let y12_2407 : ed25519_field_element_t :=
    (y11_2406) *% (c3_2388) in 
  let tv2_2408 : ed25519_field_element_t :=
    (y11_2406) *% (y11_2406) in 
  let tv2_2409 : ed25519_field_element_t :=
    (tv2_2408) *% (gxd_2395) in 
  let e1_2410 : bool :=
    (tv2_2409) =.? (gx1_2399) in 
  let y1_2411 : ed25519_field_element_t :=
    cmov (y12_2407) (y11_2406) (e1_2410) in 
  let x2n_2412 : ed25519_field_element_t :=
    (x1n_2393) *% (tv1_2391) in 
  let y21_2413 : ed25519_field_element_t :=
    (y11_2406) *% (u_2381) in 
  let y21_2414 : ed25519_field_element_t :=
    (y21_2413) *% (c2_2387) in 
  let y22_2415 : ed25519_field_element_t :=
    (y21_2414) *% (c3_2388) in 
  let gx2_2416 : ed25519_field_element_t :=
    (gx1_2399) *% (tv1_2391) in 
  let tv2_2417 : ed25519_field_element_t :=
    (y21_2414) *% (y21_2414) in 
  let tv2_2418 : ed25519_field_element_t :=
    (tv2_2417) *% (gxd_2395) in 
  let e2_2419 : bool :=
    (tv2_2418) =.? (gx2_2416) in 
  let y2_2420 : ed25519_field_element_t :=
    cmov (y22_2415) (y21_2414) (e2_2419) in 
  let tv2_2421 : ed25519_field_element_t :=
    (y1_2411) *% (y1_2411) in 
  let tv2_2422 : ed25519_field_element_t :=
    (tv2_2421) *% (gxd_2395) in 
  let e3_2423 : bool :=
    (tv2_2422) =.? (gx1_2399) in 
  let xn_2424 : ed25519_field_element_t :=
    cmov (x2n_2412) (x1n_2393) (e3_2423) in 
  let y_2425 : ed25519_field_element_t :=
    cmov (y2_2420) (y1_2411) (e3_2423) in 
  let e4_2426 : bool :=
    sgn0_m_eq_1 (y_2425) in 
  let y_2427 : ed25519_field_element_t :=
    cmov (y_2425) ((zero_2383) -% (y_2425)) (xor (e3_2423) (e4_2426)) in 
  (xn_2424, xd_2392, y_2427, one_2384).

Definition map_to_curve_elligator2_edwards25519
  (u_2428 : ed25519_field_element_t)
  : ed_point_t :=
  let j_2429 : ed25519_field_element_t :=
    nat_mod_from_literal (_) (j_v) : ed25519_field_element_t in 
  let zero_2430 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let one_2431 : ed25519_field_element_t :=
    nat_mod_one  in 
  let two_2432 : ed25519_field_element_t :=
    nat_mod_two  in 
  let c1_2433 : ed25519_field_element_t :=
    option_unwrap (sqrt ((zero_2430) -% ((j_2429) +% (two_2432)))) in 
  let '(xmn_2434, xmd_2435, ymn_2436, ymd_2437) :=
    map_to_curve_elligator2_curve25519 (u_2428) in 
  let xn_2438 : ed25519_field_element_t :=
    (xmn_2434) *% (ymd_2437) in 
  let xn_2439 : ed25519_field_element_t :=
    (xn_2438) *% (c1_2433) in 
  let xd_2440 : ed25519_field_element_t :=
    (xmd_2435) *% (ymn_2436) in 
  let yn_2441 : ed25519_field_element_t :=
    (xmn_2434) -% (xmd_2435) in 
  let yd_2442 : ed25519_field_element_t :=
    (xmn_2434) +% (xmd_2435) in 
  let tv1_2443 : ed25519_field_element_t :=
    (xd_2440) *% (yd_2442) in 
  let e_2444 : bool :=
    (tv1_2443) =.? (zero_2430) in 
  let xn_2445 : ed25519_field_element_t :=
    cmov (xn_2439) (zero_2430) (e_2444) in 
  let xd_2446 : ed25519_field_element_t :=
    cmov (xd_2440) (one_2431) (e_2444) in 
  let yn_2447 : ed25519_field_element_t :=
    cmov (yn_2441) (one_2431) (e_2444) in 
  let yd_2448 : ed25519_field_element_t :=
    cmov (yd_2442) (one_2431) (e_2444) in 
  let x_2449 : ed25519_field_element_t :=
    (xn_2445) *% (nat_mod_inv (xd_2446)) in 
  let y_2450 : ed25519_field_element_t :=
    (yn_2447) *% (nat_mod_inv (yd_2448)) in 
  (x_2449, y_2450, one_2431, (x_2449) *% (y_2450)).

Definition map_to_curve_elligator2_edwards
  (u_2451 : ed25519_field_element_t)
  : ed_point_t :=
  let st_2452 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    map_to_curve_elligator2 (u_2451) in 
  curve25519_to_edwards25519 (st_2452).

Definition ed_encode_to_curve
  (msg_2453 : byte_seq)
  (dst_2454 : byte_seq)
  : ed_point_result_t :=
  bind (ed_hash_to_field (msg_2453) (dst_2454) (usize 1)) (fun u_2455 =>
    let q_2456 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      map_to_curve_elligator2_edwards (seq_index (u_2455) (usize 0)) in 
    @Ok ed_point_t error_t (ed_clear_cofactor (q_2456))).


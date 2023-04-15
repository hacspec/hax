type bigint = Z.t
type t = bigint
val zero : Z.t
val one : Z.t
val two : Z.t
val succ_big_int : Z.t -> Z.t
val pred_big_int : Z.t -> Z.t
val minus_big_int : Z.t -> Z.t
val abs_big_int : Z.t -> Z.t
val add_big_int : Z.t -> Z.t -> Z.t
val mult_big_int : Z.t -> Z.t -> Z.t
val sub_big_int : Z.t -> Z.t -> Z.t
val div_big_int : Z.t -> Z.t -> Z.t
val mod_big_int : Z.t -> Z.t -> Z.t
val eq_big_int : Z.t -> Z.t -> bool
val le_big_int : Z.t -> Z.t -> bool
val lt_big_int : Z.t -> Z.t -> bool
val ge_big_int : Z.t -> Z.t -> bool
val gt_big_int : Z.t -> Z.t -> bool
val logand_big_int : Z.t -> Z.t -> Z.t
val logor_big_int : Z.t -> Z.t -> Z.t
val logxor_big_int : Z.t -> Z.t -> Z.t
val lognot_big_int : Z.t -> Z.t
val shift_left_big_int : Z.t -> Z.t -> Z.t
val shift_right_big_int : Z.t -> Z.t -> Z.t
val sqrt_big_int : Z.t -> Z.t
val string_of_big_int : Z.t -> string
val big_int_of_string : string -> Z.t
val of_int : int -> Z.t
val to_int : Z.t -> int
val of_int_fs : 'a -> 'a
val to_int_fs : 'a -> 'a
val of_hex : string -> Z.t

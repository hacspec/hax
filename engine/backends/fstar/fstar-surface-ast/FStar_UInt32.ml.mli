module M = Stdint.Uint32
type uint32 = M.t
type t = M.t
val n : Z.t
val uint_to_t : Z.t -> M.t
val __uint_to_t : Z.t -> M.t
val v : t -> Prims.int
val zero : M.t
val one : M.t
val ones : M.t
val add : M.t -> M.t -> M.t
val add_underspec : M.t -> M.t -> M.t
val add_mod : M.t -> M.t -> M.t
val sub : M.t -> M.t -> M.t
val sub_underspec : M.t -> M.t -> M.t
val sub_mod : M.t -> M.t -> M.t
val mul : M.t -> M.t -> M.t
val mul_underspec : M.t -> M.t -> M.t
val mul_mod : M.t -> M.t -> M.t
val to_int : t -> Z.t
val of_int : Z.t -> t
val of_native_int : int -> t
val to_native_int : t -> int
val div : M.t -> M.t -> M.t
val rem : M.t -> M.t -> M.t
val logand : M.t -> M.t -> M.t
val logxor : M.t -> M.t -> M.t
val logor : M.t -> M.t -> M.t
val lognot : M.t -> M.t
val to_string : M.t -> string
val of_string : string -> M.t
val to_string_hex : M.t -> string
val to_string_hex_pad : M.t -> string
val shift_right : M.t -> Stdint.Uint32.t -> M.t
val shift_left : M.t -> Stdint.Uint32.t -> M.t
val shift_arithmetic_right : M.t -> Stdint.Uint32.t -> M.t
val eq : t -> t -> bool
val gt : t -> t -> bool
val gte : t -> t -> bool
val lt : t -> t -> bool
val lte : t -> t -> bool
val eq_mask : t -> t -> t
val gte_mask : t -> t -> t
val op_Plus_Hat : M.t -> M.t -> M.t
val op_Plus_Question_Hat : M.t -> M.t -> M.t
val op_Plus_Percent_Hat : M.t -> M.t -> M.t
val op_Subtraction_Hat : M.t -> M.t -> M.t
val op_Subtraction_Question_Hat : M.t -> M.t -> M.t
val op_Subtraction_Percent_Hat : M.t -> M.t -> M.t
val op_Star_Hat : M.t -> M.t -> M.t
val op_Star_Question_Hat : M.t -> M.t -> M.t
val op_Star_Percent_Hat : M.t -> M.t -> M.t
val op_Slash_Hat : M.t -> M.t -> M.t
val op_Percent_Hat : M.t -> M.t -> M.t
val op_Hat_Hat : M.t -> M.t -> M.t
val op_Amp_Hat : M.t -> M.t -> M.t
val op_Bar_Hat : M.t -> M.t -> M.t
val op_Less_Less_Hat : M.t -> Stdint.Uint32.t -> M.t
val op_Greater_Greater_Hat : M.t -> Stdint.Uint32.t -> M.t
val op_Equals_Hat : t -> t -> bool
val op_Greater_Hat : t -> t -> bool
val op_Greater_Equals_Hat : t -> t -> bool
val op_Less_Hat : t -> t -> bool
val op_Less_Equals_Hat : t -> t -> bool

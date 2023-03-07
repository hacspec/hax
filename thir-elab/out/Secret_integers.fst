module Secret_integers

open Hacspec.Lib

let rotate_left (u: uint32) (s: int{s > 0 /\ s < 32}) : uint32 
  = uint32_rotate_left u s

unfold type secret_t = uint32

unfold type u8_t = uint8

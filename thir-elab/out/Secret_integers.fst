module Secret_integers

open Hacspec.Lib

let rotate_left (u: uint32) (s: int{s > 0 /\ s < 32}) : uint32 
  = uint32_rotate_left u s

unfold type secret_t = uint32

unfold type u8_t = uint8
unfold type u16_t = uint16
unfold type u32_t = uint32
unfold type u64_t = uint64
unfold type u128_t = uint128

unfold let u8 x = Hacspec.Lib.secret #U8 (pub_u8 x)
unfold let u16 x = Hacspec.Lib.secret #U16 (pub_u16 x)
unfold let u32 x = Hacspec.Lib.secret #U32 (pub_u32 x)
unfold let u64 x = Hacspec.Lib.secret #U64 (pub_u64 x)
unfold let u128 x = Hacspec.Lib.secret #U128 (pub_u128 x)



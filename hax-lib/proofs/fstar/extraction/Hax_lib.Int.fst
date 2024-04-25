module Hax_lib.Int

open Core

unfold type t_Int = int
unfold type impl__Int__to_u16

unfold let impl__Int__to_u8 (#t:inttype) (n:range_t t) : int_t t = mk_int #t n
unfold let impl__Int__to_u16 (#t:inttype) (n:range_t t) : int_t t = mk_int #t n
unfold let impl__Int__to_u32 (#t:inttype) (n:range_t t) : int_t t = mk_int #t n
unfold let impl__Int__to_u64 (#t:inttype) (n:range_t t) : int_t t = mk_int #t n
unfold let impl__Int__to_u128 (#t:inttype) (n:range_t t) : int_t t = mk_int #t n
unfold let impl__Int__to_usize (#t:inttype) (n:range_t t) : int_t t = mk_int #t n

unfold let impl__Int__to_i8 (#t:inttype) (n:range_t t) : int_t t = mk_int #t n
unfold let impl__Int__to_i16 (#t:inttype) (n:range_t t) : int_t t = mk_int #t n
unfold let impl__Int__to_i32 (#t:inttype) (n:range_t t) : int_t t = mk_int #t n
unfold let impl__Int__to_i64 (#t:inttype) (n:range_t t) : int_t t = mk_int #t n
unfold let impl__Int__to_i128 (#t:inttype) (n:range_t t) : int_t t = mk_int #t n
unfold let impl__Int__to_isize (#t:inttype) (n:range_t t) : int_t t = mk_int #t n

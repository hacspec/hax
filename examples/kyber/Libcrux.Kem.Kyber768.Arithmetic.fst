module Libcrux.Kem.Kyber768.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

type t_KyberPolynomialRingElement = { f_coefficients:array i32 256sz }
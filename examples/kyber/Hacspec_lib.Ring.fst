module Hacspec_lib.Ring
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

type t_PolynomialRingElement f v_COEFFICIENTS = { f_coefficients:array f v_COEFFICIENTS }

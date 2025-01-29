;(set-logic QF_LIA)

; let m = v % p in if m >= p/2 then m - p else m

(define-fun cast_i32 ((v Int)) Int
   (let ((m (mod v 4294967296)))
    (ite (>= m 2147483648) (- m 4294967296) m)))

(define-fun cast_i16 ((v Int)) Int
   (let ((m (mod v 65536)))
    (ite (>= m 32768) (- m 65536) m)))

(define-fun montgomery-reduce ((v Int)) Int
    (let ((k (* (cast_i32 (cast_i16 v)) 62209)))
    (let ((k_times_modulus (* (cast_i32 (cast_i16 k)) 3329)))
    (let ((c (cast_i16 (div k_times_modulus 65536))))
    (let ((value_high (cast_i16 (div v 65536))))
    (- value_high c))))))

(push)
(declare-const c Int)
(define-fun d() Int (montgomery-reduce c))

(assert (>= c (- 218103808)))
(assert (<= c 218103808))

; The following is verified to be unsat
(assert (or (<= d (- 4993))
            (>= d 4993)))

; The following does not terminate
; (assert (or (<= d (- 4993))
;             (>= d 4993)
;             (not (= (mod d 3329) (mod (* c 169) 3329)))))

(echo "Verifying Montgomery Reduce")
(check-sat)
; following did not help
; (check-sat-using (and-then qfnra-nlsat smt))
(get-model)
(pop)

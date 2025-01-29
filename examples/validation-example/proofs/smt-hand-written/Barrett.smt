;(set-logic QF_LIA)

; let m = v % p in if m >= p/2 then m - p else m

(define-fun cast_i32 ((v Int)) Int
   (let ((m (mod v 4294967296)))
    (ite (>= m 2147483648) (- m 4294967296) m)))

(define-fun cast_i16 ((v Int)) Int
   (let ((m (mod v 65536)))
    (ite (>= m 32768) (- m 65536) m)))

; pub fn barrett_reduce(value: FieldElement) -> FieldElement {
;     let t = i64::from(value) * BARRETT_MULTIPLIER;
;     // assert!(9223372036854775807 - (BARRETT_R >> 1) > t);
;     let t = t + (BARRETT_R >> 1);

;     let quotient = t >> BARRETT_SHIFT;
;     // assert!(quotient <= 2147483647_i64 || quotient >= -2147483648_i64);
;     let quotient = quotient as i32;

;     // assert!(((quotient as i64) * (FIELD_MODULUS as i64)) < 9223372036854775807);
;     let sub = quotient * FIELD_MODULUS;

;     hax::fstar!(r"Math.Lemmas.cancel_mul_mod (v $quotient) 3329");

;     value - sub
; }

(define-fun barrett-reduce ((v Int)) Int
    (let ((t (* v 20159)))
    (let ((tt (+ t 33554432)))
    (let ((q (div tt 67108864)))
    (let ((qq (cast_i32 q)))
    (let ((sub (* qq 3329)))
    (- v sub)))))))

(push)
(declare-const a Int)
(define-fun b () Int (barrett-reduce a))
(assert (>= a (- 67108864)))
(assert (<= a 67108864))

(assert (or (<= b (- 3329))
            (or (>= b 3329))
                (not (= (mod b 3329) (mod a 3329)))))

(echo "Verifying Barrett Reduce")
(check-sat)
(get-model)
(pop)


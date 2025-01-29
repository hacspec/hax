;(set-logic QF_LIA)

(declare-const p Int)
(assert (> p 0))

(declare-fun pmod (Int Int) Int)

(declare-fun montgomery-mul (Int Int) Int)
(assert (forall ((v Int) (z Int))
        (=  (pmod (montgomery-mul v z) p) (pmod (* v z) p))))

(define-sort idx () (_ BitVec 4))
(define-fun ntt-step ((v (Array idx Int)) (zeta Int) (i idx) (j idx)) (Array idx Int)
	(let ((t (montgomery-mul (select v j) zeta)))
	(let ((a_minus_t (- (select v i) t)))
	(let ((a_plus_t (+ (select v i) t)))
	(let ((v1 (store v j a_minus_t)))
	(let ((v2 (store v1 i a_plus_t)))
	v2))))))

(declare-const v0 (Array idx Int))
(declare-const zeta Int)
(declare-const i idx)
(declare-const j idx)
(define-fun v1 () (Array idx Int) (ntt-step v0 zeta i j))

(assert (not (= i j)))

(assert (forall ((a Int) (b Int))
	(= (pmod (+ a (pmod b p)) p)
	    (pmod (+ a b) p))))

(assert (forall ((a Int) (b Int))
	(= (pmod (- a (pmod b p)) p) 
           (pmod (- a b) p))))

;(assert (not (= (select v1 j)
;	        (- (select v0 i) (montgomery-mul (select v0 j) zeta)))))

;(assert (not (= (pmod (select v1 j) p)
;	         (pmod (- (select v0 i) (pmod (* (select v0 j) zeta) p)) p))))

(assert (not (= (pmod (select v1 j) p)
	         (pmod (- (select v0 i) (* (select v0 j) zeta)) p))))

(echo "Verifying NTT Step")
;(check-sat)
; following did not help
(check-sat-using (and-then qfnra-nlsat smt))
(get-model)

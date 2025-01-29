(set-logic ALL)


(define-sort bit () (_ BitVec 1))
(define-sort i16 () (_ BitVec 16))
(define-sort u8 () (_ BitVec 8))

(define-sort idx16 () (_ BitVec 4))
(define-sort idx8 () (_ BitVec 1))

(define-sort PortableVector () (Array idx16 i16))
(define-sort Output () (Array bit u8))

(define-fun load_u8 ((ns PortableVector) (i idx16)) u8
  ( (_ extract 7 0) (bvand #x00ff (select ns i))))

(echo "sanity checks...")
(push)
 (declare-const pv PortableVector)
 (assert (not (= (load_u8 pv #x0) #x00)))
 (echo "want sat")
 (check-sat)
(pop)

(push)
 (declare-const pv PortableVector)
 (assert (= (select pv #x0) #x0121))
 (assert (= (load_u8 pv #x0) #x21))
 (echo "want sat")
 (check-sat)
(pop)

(push)
 (declare-const pv PortableVector)
 (assert (not (=> 
    (= (select pv #x0) #x0121)
    (= (load_u8 pv #x0) #x21))))
 (echo "want unsat")
 (check-sat)
(pop)

(define-fun u8_as_bit ((n u8)) bit ((_ int2bv 1) (bv2nat n)))
(define-fun idx16_as_idx ((n idx16)) idx8 ((_ int2bv 1) (bv2nat (bvlshr n #x3))))

(define-fun
  serialize-1
  ((v PortableVector))
  Output
  (let
    ( (o0 (bvor (bvshl (load_u8 v #x0) #x00)
                (bvshl (load_u8 v #x1) #x01)
                (bvshl (load_u8 v #x2) #x02)
                (bvshl (load_u8 v #x3) #x03)
                (bvshl (load_u8 v #x4) #x04)
                (bvshl (load_u8 v #x5) #x05)
                (bvshl (load_u8 v #x6) #x06)
                (bvshl (load_u8 v #x7) #x07)))
      (o1 (bvor (bvshl (load_u8 v #x8) #x00)
                (bvshl (load_u8 v #x9) #x01)
                (bvshl (load_u8 v #xa) #x02)
                (bvshl (load_u8 v #xb) #x03)
                (bvshl (load_u8 v #xc) #x04)
                (bvshl (load_u8 v #xd) #x05)
                (bvshl (load_u8 v #xe) #x06)
                (bvshl (load_u8 v #xf) #x07))))
      (store (store ((as const Output) #x00) #b0 o0) #b1 o1)))

(define-fun
  get-bit-pv
  ( (pv PortableVector)
    (i idx16))
  bit
  ( (_ int2bv 1) (bv2nat (bvand (select pv i) #x0001) )))


(define-fun
  get-bit-packed
  ( (o Output)
    (i idx16))
  bit
  (let
    ( (chunk (select o (idx16_as_idx i)))
      (imod (bvurem i #x8)))
    (u8_as_bit (bvlshr chunk (concat #x0 imod)))))


(declare-const i idx16)
(declare-const pv PortableVector)
(declare-const o Output)

(define-fun i16-is-bitty ((v i16)) Bool
  (= #x0000 (bvand #xfffe v)))

(define-fun PortableVector-is-bitty ((v PortableVector)) Bool
  (forall ((i idx16)) (i16-is-bitty (select v i))))

(echo "real check: (want unsat)")

; asking for the opposite to find counterexamples
(assert (not
      ; the precondition
  (=> (and  (PortableVector-is-bitty pv)) ; values need to be bits
            (= o (serialize-1 pv))        ; put the two in relation wrt the encoding
      ; the postcondition: get-bit is the same
      (=  (get-bit-packed o  i)
          (get-bit-pv     pv i)))))

(check-sat)

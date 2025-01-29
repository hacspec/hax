;; Function-Def lib_verus::main
;; lib_verus.rs:133:1: 133:10 (#0)
(get-info :all-statistics)
(push)
 (declare-const no%param Int)
 (declare-const tmp%1 core!result.Result.)
 (declare-const tmp%2 Poly)
 (declare-const tmp%3 core!result.Result.)
 (declare-const tmp%4 Poly)
 (declare-const proto@0 lib_verus!ProtocolLibrary.)
 (declare-const msg@ lib_verus!UnverifiedMessage.)
 (declare-const msg$1@ lib_verus!VerifiedMessage.)
 (assert
  fuel_defaults
 )
 (declare-const proto@1 lib_verus!ProtocolLibrary.)
 (declare-const proto@2 lib_verus!ProtocolLibrary.)
 ;; possible arithmetic underflow/overflow
 (declare-const %%location_label%%0 Bool)
 ;; possible arithmetic underflow/overflow
 (declare-const %%location_label%%1 Bool)
 ;; possible arithmetic underflow/overflow
 (declare-const %%location_label%%2 Bool)
 ;; possible arithmetic underflow/overflow
 (declare-const %%location_label%%3 Bool)
 ;; precondition not satisfied
 (declare-const %%location_label%%4 Bool)
 ;; precondition not satisfied
 (declare-const %%location_label%%5 Bool)
 (assert
  (not (=>
    (ens%lib_verus!impl&%4.default. 0 proto@0)
    (and
     (=>
      %%location_label%%0
      (uInv SZ (Mul 2 3))
     )
     (and
      (=>
       %%location_label%%1
       (uInv SZ (Mul 3 42))
      )
      (and
       (=>
        %%location_label%%2
        (uInv SZ (Add (uClip SZ (Mul 2 3)) (uClip SZ (Mul 3 42))))
       )
       (and
        (=>
         %%location_label%%3
         (uInv SZ (Add (uClip SZ (Add (uClip SZ (Mul 2 3)) (uClip SZ jj3 42)))) 5))
        )
        (=>
         (= msg@ (lib_verus!UnverifiedMessage./UnverifiedMessage (%I (I 3)) (%I (I (uClip SZ (Add
               (uClip SZ (Add (uClip SZ (Mul 2 3)) (uClip SZ (Mul 3 42)))) 5
            )))
           ) (%I (I 1)) (%I (I 42))
         ))
         (=>
          (has_type (Poly%lib_verus!ProtocolLibrary. proto@1) TYPE%lib_verus!ProtocolLibrary.)
          (=>
           (ens%lib_verus!impl&%8.validate. proto@0 proto@1 msg@ tmp%1)
           (and
            (=>
             %%location_label%%4
             (req%core!result.impl&%0.unwrap. $ TYPE%lib_verus!VerifiedMessage. $ TYPE%lib_verus!Error.
              tmp%1
            ))
            (=>
             (ens%core!result.impl&%0.unwrap. $ TYPE%lib_verus!VerifiedMessage. $ TYPE%lib_verus!Error.
              tmp%1 tmp%2
             )
             (=>
              (= msg$1@ (%Poly%lib_verus!VerifiedMessage. tmp%2))
              (=>
               (has_type (Poly%lib_verus!ProtocolLibrary. proto@2) TYPE%lib_verus!ProtocolLibrary.)
               (=>
                (ens%lib_verus!impl&%8.apply. proto@1 proto@2 msg$1@ tmp%3)
                (=>
                 %%location_label%%5
                 (req%core!result.impl&%0.unwrap. $ TYPE%tuple%0. $ TYPE%lib_verus!Error. tmp%3)
 ))))))))))))))))
 (get-info :version)
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
 (get-info :reason-unknown)
 (get-model)
 (assert
  (not %%location_label%%4)
 )
 (get-info :version)
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
 (get-info :reason-unknown)
 (get-model)
 (assert
  (not %%location_label%%5)
 )
 (get-info :version)
 (assert
  true
 )
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)


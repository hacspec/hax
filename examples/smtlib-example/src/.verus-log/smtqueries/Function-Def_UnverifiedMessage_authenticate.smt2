;; Function-Def lib_verus::UnverifiedMessage::authenticate
;; lib_verus.rs:52:5: 52:35 (#0)
(get-info :all-statistics)
(push)
 (declare-const %return! Bool)
 (declare-const self! lib_verus!UnverifiedMessage.)
 (assert
  fuel_defaults
 )
 (assert
  (has_type (Poly%lib_verus!UnverifiedMessage. self!) TYPE%lib_verus!UnverifiedMessage.)
 )
 ;; possible arithmetic underflow/overflow
 (declare-const %%location_label%%0 Bool)
 ;; possible arithmetic underflow/overflow
 (declare-const %%location_label%%1 Bool)
 ;; possible arithmetic underflow/overflow
 (declare-const %%location_label%%2 Bool)
 ;; possible arithmetic underflow/overflow
 (declare-const %%location_label%%3 Bool)
 ;; possible arithmetic underflow/overflow
 (declare-const %%location_label%%4 Bool)
 (assert
  (not (and
    (=>
     %%location_label%%0
     (uInv SZ (Mul 2 (lib_verus!UnverifiedMessage./UnverifiedMessage/sender (%Poly%lib_verus!UnverifiedMessage.
         (Poly%lib_verus!UnverifiedMessage. self!)
    )))))
    (and
     (=>
      %%location_label%%1
      (uInv SZ (Mul 3 (lib_verus!UnverifiedMessage./UnverifiedMessage/value (%Poly%lib_verus!UnverifiedMessage.
          (Poly%lib_verus!UnverifiedMessage. self!)
     )))))
     (and
      (=>
       %%location_label%%2
       (uInv SZ (Add (uClip SZ (Mul 2 (lib_verus!UnverifiedMessage./UnverifiedMessage/sender
            (%Poly%lib_verus!UnverifiedMessage. (Poly%lib_verus!UnverifiedMessage. self!))
          ))
         ) (uClip SZ (Mul 3 (lib_verus!UnverifiedMessage./UnverifiedMessage/value (%Poly%lib_verus!UnverifiedMessage.
             (Poly%lib_verus!UnverifiedMessage. self!)
      )))))))
      (and
       (=>
        %%location_label%%3
        (uInv SZ (Mul 5 (lib_verus!UnverifiedMessage./UnverifiedMessage/timestamp (%Poly%lib_verus!UnverifiedMessage.
            (Poly%lib_verus!UnverifiedMessage. self!)
       )))))
       (=>
        %%location_label%%4
        (uInv SZ (Add (uClip SZ (Add (uClip SZ (Mul 2 (lib_verus!UnverifiedMessage./UnverifiedMessage/sender
               (%Poly%lib_verus!UnverifiedMessage. (Poly%lib_verus!UnverifiedMessage. self!))
             ))
            ) (uClip SZ (Mul 3 (lib_verus!UnverifiedMessage./UnverifiedMessage/value (%Poly%lib_verus!UnverifiedMessage.
                (Poly%lib_verus!UnverifiedMessage. self!)
           )))))
          ) (uClip SZ (Mul 5 (lib_verus!UnverifiedMessage./UnverifiedMessage/timestamp (%Poly%lib_verus!UnverifiedMessage.
              (Poly%lib_verus!UnverifiedMessage. self!)
 )))))))))))))
 (get-info :version)
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
 (get-info :reason-unknown)
 (get-model)
 (assert
  (not %%location_label%%0)
 )
 (get-info :version)
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
 (get-info :reason-unknown)
 (get-model)
 (assert
  (not %%location_label%%1)
 )
(pop)

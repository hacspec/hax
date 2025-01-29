;; Function-Recommends lib_verus::ProtocolLibrary::validate
;; lib_verus.rs:68:5: 68:86 (#0)
(get-info :all-statistics)
(push)
 (declare-const %return! core!result.Result.)
 (declare-const self!@0 lib_verus!ProtocolLibrary.)
 (declare-const msg! lib_verus!UnverifiedMessage.)
 (declare-const tmp%1 Bool)
 (declare-const tmp%2 Int)
 (declare-const tmp%3 lib_verus!State.)
 (declare-const verification_id@ Int)
 (assert
  fuel_defaults
 )
 (assert
  (has_type (Poly%lib_verus!ProtocolLibrary. self!@0) TYPE%lib_verus!ProtocolLibrary.)
 )
 (assert
  (has_type (Poly%lib_verus!UnverifiedMessage. msg!) TYPE%lib_verus!UnverifiedMessage.)
 )
 (declare-const self!@1 lib_verus!ProtocolLibrary.)
 (declare-const self!@2 lib_verus!ProtocolLibrary.)
 (declare-const %%switch_label%%0 Bool)
 (declare-const %%switch_label%%1 Bool)
 (declare-const %%switch_label%%2 Bool)
 (assert
  (not (or
    (=>
     (not (not (let
        ((tmp%%$ (lib_verus!ProtocolLibrary./ProtocolLibrary/state (%Poly%lib_verus!ProtocolLibrary.
            (Poly%lib_verus!ProtocolLibrary. self!@0)
        ))))
        (is-lib_verus!State./Idle tmp%%$)
     )))
     %%switch_label%%2
    )
    (and
     (not %%switch_label%%2)
     (or
      (=>
       (not (not tmp%1))
       %%switch_label%%1
      )
      (and
       (not %%switch_label%%1)
       (or
        (=>
         (not (< (lib_verus!UnverifiedMessage./UnverifiedMessage/timestamp (%Poly%lib_verus!UnverifiedMessage.
             (Poly%lib_verus!UnverifiedMessage. msg!)
            )
           ) (lib_verus!ProtocolLibrary./ProtocolLibrary/last_changed (%Poly%lib_verus!ProtocolLibrary.
             (Poly%lib_verus!ProtocolLibrary. self!@0)
         ))))
         %%switch_label%%0
        )
        (not %%switch_label%%0)
 )))))))
 (get-info :version)
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)


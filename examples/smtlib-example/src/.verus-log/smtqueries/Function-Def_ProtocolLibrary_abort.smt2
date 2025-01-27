;; Function-Def lib_verus::ProtocolLibrary::abort
;; lib_verus.rs:112:5: 112:45 (#0)
(get-info :all-statistics)
(push)
 (declare-const %return! core!result.Result.)
 (declare-const self!@0 lib_verus!ProtocolLibrary.)
 (declare-const tmp%1 lib_verus!State.)
 (assert
  fuel_defaults
 )
 (assert
  (has_type (Poly%lib_verus!ProtocolLibrary. self!@0) TYPE%lib_verus!ProtocolLibrary.)
 )
 (declare-const self!@1 lib_verus!ProtocolLibrary.)
 (declare-const %%switch_label%%0 Bool)
 (assert
  (not (or
    (=>
     (not (not (let
        ((tmp%%$ (lib_verus!ProtocolLibrary./ProtocolLibrary/state (%Poly%lib_verus!ProtocolLibrary.
            (Poly%lib_verus!ProtocolLibrary. self!@0)
        ))))
        (is-lib_verus!State./WaitToApply tmp%%$)
     )))
     %%switch_label%%0
    )
    (not %%switch_label%%0)
 )))
 (get-info :version)
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)


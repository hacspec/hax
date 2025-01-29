;; Function-Recommends lib_verus::main
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
 (assert
  (not true)
 )
 (get-info :version)
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)


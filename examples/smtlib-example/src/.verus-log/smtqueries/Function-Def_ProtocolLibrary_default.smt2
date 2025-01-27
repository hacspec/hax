;; Function-Def lib_verus::ProtocolLibrary::default
;; lib_verus.rs:29:5: 29:25 (#0)
(get-info :all-statistics)
(push)
 (declare-const %return! lib_verus!ProtocolLibrary.)
 (declare-const no%param Int)
 (assert
  fuel_defaults
 )
 (assert
  (not true)
 )
 (get-info :version)
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)


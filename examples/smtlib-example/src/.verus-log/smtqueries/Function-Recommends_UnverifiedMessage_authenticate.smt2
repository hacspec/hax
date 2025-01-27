;; Function-Recommends lib_verus::UnverifiedMessage::authenticate
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
 (assert
  (not true)
 )
 (get-info :version)
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)


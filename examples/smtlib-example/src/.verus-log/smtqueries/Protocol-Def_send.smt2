;; Function-Def lib_verus::send
;; lib_verus.rs:126:1: 126:63 (#0)
(get-info :all-statistics)
(push)
 (declare-const %return! Bool)
 (declare-const sender! Int) (declare-const timestamp! Int)
 (declare-const value! Int)
 (assert
  fuel_defaults
 )
 (assert
  (uInv SZ sender!)
 )
 (assert
  (uInv SZ timestamp!)
 )
 (assert
  (uInv SZ value!)
 )
 (assert
  (not true)
 )
 (get-info :version)
 (set-option :rlimit 30000000)
 (check-sat)
 (set-option :rlimit 0)
(pop)


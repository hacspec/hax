;;; This example doesn't translate the code, but captures the control-flow graph of the example in
;;; SMT-LIB.
;;;
;;; Nodes are function calls (with concrete values, but these values might be opaque) and edges are
;;; relations between two function calls. Two functions share an edge iff the relation is true.
;;;
;;; In the future, we might experiment with more fine-grained, e.g. each block being a node.

;;; Let's see if we can work with non-opaque types for now and copy the types from the other
;;; example.

;; The unit type, aka the empty/zero-element tuple.
(declare-datatype s/Unit ((sc/Unit)))

;; The core::result::Result enum
(declare-datatype e/Result
  (par (T E)
    ( (ev/Result/Ok (evd/Result/Ok T))
      (ev/Result/Err (evd/Result/Err E)))) )

;; The Error enum from the example code
(declare-datatype e/Error
  ( ( ev/Error/AuthenticationFailed )
    ( ev/Error/MessageTooOld )
    ( ev/Error/NotAcceptingNew )
    ( ev/Error/NotReadyToApply )
    ( ev/Error/UnexpectedVerifiedMsg )))

;; The ProtocolLibrary struct from the example code
(declare-datatype s/ProtocolLibrary
  ( (sc/ProtocolLibrary
      (sd/ProtocolLibrary/value Int)
      (sd/ProtocolLibrary/last_changed Int))))

;; The UnverifiedMessage struct from the example code
(declare-datatype s/UnverifiedMessage
  ( (sc/UnverifiedMessage
      (sd/UnverifiedMessage/sender Int)
      (sd/UnverifiedMessage/timestamp Int)
      (sd/UnverifiedMessage/value Int)
      (sd/UnverifiedMessage/authenticator Int))))

;; The VerifiedMessage struct from the example code
(declare-datatype s/VerifiedMessage
  ( (sc/VerifiedMessage
      (sd/VerifiedMessage/sender Int)
      (sd/VerifiedMessage/timestamp Int)
      (sd/VerifiedMessage/value Int)
      (sd/VerifiedMessage/state_last_changed Int))))

;;; Now, declare the function call nodes. These are datatypes here, containing the call arguments.

(declare-datatype f/send
  ( (fc/send
      (fd/send/sender Int)
      (fd/send/timestamp Int)
      (fd/send/value Int))))

(declare-datatype fm/UnverifiedMessage/authenticate
  ( (fmc/UnverifiedMessage/authenticate
      (fmd/UnverifiedMessage/authenticate/self s/UnverifiedMessage))))

(declare-datatype fm/ProtocolLibrary/validate
  ( (fmc/ProtocolLibrary/validate 
      (fmd/ProtocolLibrary/validate/self s/ProtocolLibrary)
      (fmd/ProtocolLibrary/validate/msg  s/UnverifiedMessage))))

(declare-datatype fm/ProtocolLibrary/apply
    ( (fmc/ProtocolLibrary/apply   
        (fmd/ProtocolLibrary/apply/self s/ProtocolLibrary)
        (fmd/ProtocolLibrary/apply/msg  s/VerifiedMessage))))

;;; Next we declare the relations between the edges. 

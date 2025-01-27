(set-logic ALL)

(declare-datatype ~Panicking
  (par (T)
    ( (~Cont (~Cont/get T))
      (~Panic))))

(declare-datatype ~Mutable
  (par (S R)
    ( (~mut (~mut/self S)
            (~mut/return R )))))

(declare-datatype e/Result
  (par (T E)
    ( (ev/Result/Ok (evd/Result/Ok T))
      (ev/Result/Err (evd/Result/Err E)))) )

(declare-datatype e/Error
  ( ( ev/Error/AuthenticationFailed )
    ( ev/Error/MessageTooOld )
    ( ev/Error/NotAcceptingNew )
    ( ev/Error/NotReadyToApply )
    ( ev/Error/UnexpectedVerifiedMsg )))

(declare-datatype e/State
  ( ( ev/State/Idle )
    ( ev/State/WaitToApply (evd/State/WaitToApply Int) )))

(declare-datatype s/ProtocolLibrary
  ( (sc/ProtocolLibrary
      (sd/ProtocolLibrary/state e/State)
      (sd/ProtocolLibrary/value Int)
      (sd/ProtocolLibrary/last_changed Int)
      (sd/ProtocolLibrary/msg_ctr Int))))

(declare-datatype s/UnverifiedMessage
  ( (sc/UnverifiedMessage
      (sd/UnverifiedMessage/sender Int)
      (sd/UnverifiedMessage/authenticator Int)
      (sd/UnverifiedMessage/timestamp Int)
      (sd/UnverifiedMessage/value Int))))


(declare-datatype s/VerifiedMessage
  ( (sc/VerifiedMessage
      (sd/VerifiedMessage/sender Int)
      (sd/VerifiedMessage/timestamp Int)
      (sd/VerifiedMessage/value Int)
      (sd/VerifiedMessage/verification_id Int))))

(define-fun
  fm/UnverifiedMessage/authenticate
  ((self s/UnverifiedMessage))
  Bool
  (= (sd/UnverifiedMessage/authenticator self)
     (+ (* 2 (sd/UnverifiedMessage/sender self))
        (* 3 (sd/UnverifiedMessage/value self))
        (* 5 (sd/UnverifiedMessage/timestamp self)))))

(define-fun
  fm/ProtocolLibrary/validate
  ( (self s/ProtocolLibrary)
    (msg s/UnverifiedMessage))
  (~Panicking (~Mutable s/ProtocolLibrary (e/Result s/VerifiedMessage e/Error)))
  (ite
    (is-ev/State/Idle (sd/ProtocolLibrary/state self))
    (~Cont (~mut self ((as ev/Result/Err (e/Result s/VerifiedMessage e/Error)) ev/Error/NotAcceptingNew)))
    (ite
      (not (fm/UnverifiedMessage/authenticate msg))
      (~Cont (~mut self ((as ev/Result/Err (e/Result s/VerifiedMessage e/Error)) ev/Error/AuthenticationFailed)))
      (ite
        (<  (sd/UnverifiedMessage/timestamp msg)
            (sd/ProtocolLibrary/last_changed self))
        (~Cont (~mut self ((as ev/Result/Err (e/Result s/VerifiedMessage e/Error)) ev/Error/MessageTooOld)))
        (let
          ( ( verification_id 
              (sd/ProtocolLibrary/msg_ctr self)))
          (let
            ( ( self~
                (sc/ProtocolLibrary
                  (ev/State/WaitToApply verification_id)
                  (sd/ProtocolLibrary/value self)
                  (sd/ProtocolLibrary/last_changed self)
                  (sd/ProtocolLibrary/msg_ctr self))))

            (~Cont (~mut self~
              ((as ev/Result/Ok (e/Result s/VerifiedMessage e/Error))
                (sc/VerifiedMessage
                  (sd/UnverifiedMessage/sender msg)
                  (sd/UnverifiedMessage/timestamp msg)
                  (sd/UnverifiedMessage/value msg)
                  verification_id))))))))))


(declare-const lib  s/ProtocolLibrary)
(declare-const lib~ s/ProtocolLibrary)
(declare-const umsg s/UnverifiedMessage)
(declare-const vmsg s/VerifiedMessage)

(assert (=  (~Cont (~mut lib~ ((as ev/Result/Ok (e/Result s/VerifiedMessage e/Error)) vmsg)))
            (fm/ProtocolLibrary/validate lib umsg)))

(check-sat)
(get-model)

(set-logic ALL)

;; Let's treat any function as panicking, or having verification assertions.
;; - If a function returns successfully, it returns a ~cont (for continue, is there a better name?).
;; - If it panics, it returns ~panic.
;; - If it has a verification assertion (i.e. something like hax_lib::assert) and that fails, it
    returns ~assert-failed.
(declare-datatype ~Panicking
  (par (T)
    ( (~cont (~cont/get T))
      (~panic)
      (~assert-failed))))

;; Methods with &mut not only return the return value, but also the updated self.
(declare-datatype ~Mutable
  (par (S R)
    ( (~mut (~mut/self S)
            (~mut/return R )))))

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

;; The opaque function send from the example code
(declare-fun send (Int Int Int) Bool)

;; The opaque function authenticate from the example code
(declare-fun
  fm/UnverifiedMessage/authenticate
  ((s/UnverifiedMessage))
  Bool)

;; The method ProtocolLibrary::validate from the example code
(define-fun
  fm/ProtocolLibrary/validate
  ( (self s/ProtocolLibrary)
    (msg s/UnverifiedMessage))
  (~Panicking (e/Result s/VerifiedMessage e/Error))
  (ite
    (not (fm/UnverifiedMessage/authenticate msg))
    (~cont ((as ev/Result/Err (e/Result s/VerifiedMessage e/Error)) ev/Error/AuthenticationFailed))
    (ite
      (<= (sd/UnverifiedMessage/timestamp msg)
          (sd/ProtocolLibrary/last_changed self))
      (~cont ((as ev/Result/Err (e/Result s/VerifiedMessage e/Error)) ev/Error/MessageTooOld))
      (let
        ( ( self~
            (sc/ProtocolLibrary
              (sd/ProtocolLibrary/value self)
              (sd/ProtocolLibrary/last_changed self))))
        (~cont 
          ((as ev/Result/Ok (e/Result s/VerifiedMessage e/Error))
            (sc/VerifiedMessage
              (sd/UnverifiedMessage/sender msg)
              (sd/UnverifiedMessage/timestamp msg)
              (sd/UnverifiedMessage/value msg)
              (sd/ProtocolLibrary/last_changed self))))))))

;; The method ProtocolLibrary::apply from the example code
(define-fun
  fm/ProtocolLibrary/apply
  ( (self s/ProtocolLibrary)
    (msg  s/VerifiedMessage))
  (~Panicking (~Mutable s/ProtocolLibrary (e/Result s/Unit e/Error)))
  (ite
    (not (= (sd/ProtocolLibrary/last_changed self) (sd/VerifiedMessage/state_last_changed msg)))
    (~cont (~mut self ((as ev/Result/Err (e/Result s/Unit e/Error)) ev/Error/UnexpectedVerifiedMsg)))
    (ite
      (not (send (sd/VerifiedMessage/sender msg) (sd/VerifiedMessage/timestamp msg) (sd/VerifiedMessage/value msg)))
      (as ~assert-failed (~Panicking (~Mutable s/ProtocolLibrary (e/Result s/Unit e/Error))))
      (ite
        (<= (sd/VerifiedMessage/timestamp msg) (sd/ProtocolLibrary/last_changed self))
        (as ~assert-failed (~Panicking (~Mutable s/ProtocolLibrary (e/Result s/Unit e/Error))))
        (let
          ( ( self~
              (sc/ProtocolLibrary
                (sd/VerifiedMessage/value msg)
                (sd/VerifiedMessage/timestamp msg))))
          (~cont (~mut self~ ((as ev/Result/Ok (e/Result s/Unit e/Error)) sc/Unit))))))))


;; Precondition of UnverifiedMessage::authenticate
(define-fun
  pmf/UnverifiedMessage/authenticate/requires
  ((msg  s/UnverifiedMessage))
  Bool 
  true)

;; Postcondition of UnverifiedMessage::authenticate
(define-fun
  pmf/UnverifiedMessage/authenticate/ensures
  ( (msg  s/UnverifiedMessage)
    (~return Bool))
  Bool 
  (=> ~return
      (send
        (sd/UnverifiedMessage/sender msg)
        (sd/UnverifiedMessage/timestamp msg)
        (sd/UnverifiedMessage/value msg))))

;; Precondition of ProtocolLibrary::apply
(define-fun
  pmf/ProtocolLibrary/apply/requires
  ( (self s/ProtocolLibrary)
    (msg  s/VerifiedMessage))
  Bool 
  (exists 
    ( (s  s/ProtocolLibrary)
      (um s/UnverifiedMessage))
    (=  (fm/ProtocolLibrary/validate s um)
        (~cont  ( (as ev/Result/Ok
                      (e/Result s/VerifiedMessage e/Error))
                  msg)))))

;; Postcondition of ProtocolLibrary::apply
(define-fun
  pmf/ProtocolLibrary/apply/ensures
  ( (self s/ProtocolLibrary)
    (msg  s/VerifiedMessage)
    (~return (~Panicking (~Mutable s/ProtocolLibrary (e/Result s/Unit e/Error)))))
  Bool 
  (is-~cont ~return))

;;;

;; it's an opaque function without preconditions, so we can just require it holds
(assert (forall
  ((arg/msg s/UnverifiedMessage))
  (pmf/UnverifiedMessage/authenticate/ensures
    arg/msg
    (fm/UnverifiedMessage/authenticate arg/msg))))

;; check ProtocolLibrary/apply claim
(push)
  ; args
  (declare-const arg/self s/ProtocolLibrary)
  (declare-const arg/msg  s/VerifiedMessage)

  ; return value
  (define-fun
    ret
    ()
    (~Panicking (~Mutable s/ProtocolLibrary (e/Result s/Unit e/Error)))
    (fm/ProtocolLibrary/apply arg/self arg/msg))

  ; debug stuff
  (declare-const simple-ret (~Panicking (~Mutable s/ProtocolLibrary (e/Result s/Unit e/Error))))
  ;(declare-const s s/ProtocolLibrary)
  (declare-const um s/UnverifiedMessage)
  (assert (= ret simple-ret))
  (assert (=  (fm/ProtocolLibrary/validate arg/self um)
              (~cont  ( (as ev/Result/Ok
                            (e/Result s/VerifiedMessage e/Error))
                        arg/msg))))

  (assert (not (=>
    (pmf/ProtocolLibrary/apply/requires arg/self arg/msg)
    (pmf/ProtocolLibrary/apply/ensures arg/self arg/msg ret))))

  (echo "CHECK ProtocolLibrary::apply")
  (check-sat)
  (get-model)
(pop)

;; we checked that this holds for valid inputs, can assume it now
(assert (forall
  ( (arg/self s/ProtocolLibrary)
    (arg/msg  s/VerifiedMessage))
  (pmf/ProtocolLibrary/apply/ensures
    arg/self
    arg/msg
    (fm/ProtocolLibrary/apply arg/self arg/msg))))

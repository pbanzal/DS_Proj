(set-option :auto-config false)                                                
(set-option :smt.mbqi true)                                                    
(set-option :smt.macro-finder true)                                            

; Type of Message
(declare-sort Message)
; Nat datatype                                                                
(declare-datatypes ()
    ((Nat O (S (pred Nat)))))
(define-sort Time () Nat)

; ReceiveSet and DeliverSet
(declare-fun rcvQ (Time Message) Bool)
(declare-fun dvrQ (Time Message) Bool)

(define-fun incRcv ((t Time)(m Message)) Bool
  (forall ((m1 Message))
    (= (rcvQ (S t) m1) (or (rcvQ t m1) (= m1 m)))))

(define-fun incDvr ((t Time)(m Message)) Bool
  (forall ((m1 Message))
    (= (dvrQ (S t) m1) (or (dvrQ t m1) (= m1 m)))))

(define-fun invRcv ((t Time)) Bool
  (forall ((m1 Message))
    (= (rcvQ (S t) m1) (rcvQ t m1))))

(define-fun invDvr ((t Time)) Bool
  (forall ((m1 Message))
    (= (dvrQ (S t) m1) (dvrQ t m1))))

(define-fun decRcv ((t Time)(m Message)) Bool
  (forall ((m1 Message))
    (= (rcvQ (S t) m1) (and (rcvQ t m1) (not (= m1 m))))))

; sending at time t
; sending is actually incrementing rcv set
(define-fun sendMsg ((t Time)(m Message)) Bool
  (incRcv t m))

; receiving at time t
(define-fun rcvMsg ((t Time)) Bool
  (exists ((m Message))
     (and (= (rcvQ t m) true)
          (decRcv t m)
          (incDvr t m))))


; At time t, rcvQ is empty.
(define-fun isRcvQEmpty ((t Time)) Bool
  (forall ((m Message)) (= (rcvQ t m) false)))

; Initial State Predicate - at time=0                                         
(declare-const Init Bool)
(assert (= Init
  (and (forall ((m Message))
          (= (rcvQ O m) false))
       (forall ((m Message))
          (= (dvrQ O m) false)))
))

; Next State Predicate, on any given time t.
(declare-const Next Bool)
(declare-const t Time)
(assert (= Next
  (forall ((t Time))
    (xor (exists ((m Message))
            (sendMsg t m))
         (rcvMsg t)
         (and (invRcv t) (invDvr t))
    ))))
(check-sat)

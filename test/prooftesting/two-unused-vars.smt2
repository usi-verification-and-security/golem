(set-logic HORN)
(declare-fun P (Int) Bool)

(assert (forall ((x Int) (unused Int) (unused2 Bool)) (=> (= x 0) (P x))))

(assert (forall ((x Int)) (=> (P x) false)))


(check-sat)
(exit)


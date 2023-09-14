(set-logic HORN)
(declare-fun Q (Int) Bool)
(declare-fun P (Int) Bool)

(assert (forall ((x Int) (unused Int)) (=> (= x 0) (P x))))

(assert (forall ((x Int)) (=> (= x 0) (Q x))))

(assert (forall ((x Int)) (=> (Q x) false)))

(check-sat)
(exit)


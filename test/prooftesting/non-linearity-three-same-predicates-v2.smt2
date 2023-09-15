(set-logic HORN)
(declare-fun Q (Int) Bool)
(declare-fun P (Int Int) Bool)

(assert (forall ((x Int) (y Int)) (=> (= x 0) (P x y))
))


(assert (forall ((x Int) (a0 Int) (a1 Int) (a2 Int) (y Int))
    (=> (and (P x a0) (P x a1) (P x a2) (= y (+ a0 a1 a2))) (Q y))
))


(assert (forall ((x Int))
    (=> (Q x) false)
))

(check-sat)
(exit)

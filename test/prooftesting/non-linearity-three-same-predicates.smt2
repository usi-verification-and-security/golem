(set-logic HORN)
(declare-fun Q (Int) Bool)
(declare-fun P (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (P x))
))


(assert (forall ((x Int) (y Int) (z Int) (a Int))
    (=> (and (P x) (P y) (P z) (= a (+ x y z))) (Q a))
))


(assert (forall ((x Int))
    (=> (Q x) false)
))

(check-sat)
(exit)

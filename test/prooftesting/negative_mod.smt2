(set-logic HORN)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (=> (and (< x 0) (= (mod x 3) 1)) (Q x))
))


(assert (forall ((x Int))
    (=> (Q x) false)
))

(check-sat)

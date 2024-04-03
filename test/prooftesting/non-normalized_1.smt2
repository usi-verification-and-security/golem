(set-logic HORN)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Q x)))
)
(assert (forall ((x Int)) (=> (Q x) (Q (+ x 1))))
)


(assert (forall ((x Int))
    (=> (and (Q x) (> x 1)) false)
))

(check-sat)

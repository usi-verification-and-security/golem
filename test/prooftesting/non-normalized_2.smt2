(set-logic HORN)
(declare-fun Q (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (> y x) (Q x y)))
)

(assert (forall ((x Int))
    (=> (Q x (+ 1 x)) false)
))

(check-sat)

(set-logic HORN)
(declare-fun Q (Int) Bool)
(declare-fun P (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (P x))
))

(assert (forall ((x Int)) (=> (= x 0) (Q x))
))

(assert (forall ((x Int) (xp Int)) 
    (=> (and (Q x) (= xp (+ x 1))) (Q xp))
))

(assert (forall ((x Int) (xp Int)) 
    (=> (and (P x) (= xp (+ x 1))) (P xp))
))


(assert (forall ((x Int) (y Int))
    (=> (and (P x) (Q y) (>= x 1) (>= y 1)) false)
))

(check-sat)
(exit)

(set-logic HORN)

(declare-fun P (Int) Bool)

(assert (forall ( (x Int) ) (=> (> x 0) (P x))
))

(assert
  (forall ( (x Int) (y Int) ) 
    (=>
      (and
        (P x)
        (> x y)
      )
      false
    )
  )
)

(check-sat)
(exit)

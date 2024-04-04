; ./prepared/hcai/./svcomp/O3/id_o3_false-unreach-call_000.smt2
(set-logic HORN)


(declare-fun |main@entry| ( Int ) Bool)
(declare-fun |main@id.exit.split| ( ) Bool)

(assert
  (forall ( (A Int) ) 
    (=>
      (and
        true
      )
      (main@entry A)
    )
  )
)
(assert
  (forall ( (A Int) ) 
    (=>
      (main@entry A)
      main@id.exit.split
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        main@id.exit.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)

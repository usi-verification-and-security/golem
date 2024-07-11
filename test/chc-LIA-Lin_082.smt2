; ./eldarica-misc/./LIA/reve/011b-horn_000.smt2
(set-logic HORN)

(declare-fun |REC_f_| ( Int Int ) Bool)
(declare-fun |REC_f_f| ( Int Int Int Int ) Bool)
(declare-fun |CHC_COMP_FALSE| ( ) Bool)
(declare-fun |REC__f| ( Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (REC__f D C)
        (and (= A (+ 2 D)) (>= A 2) (<= C (- 3)) (= B 0))
      )
      (REC__f A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (REC__f D C)
        (and (= C (+ (- 2) B)) (>= A 2) (not (<= C (- 3))) (= A (+ 2 D)))
      )
      (REC__f A B)
    )
  )
)
(assert
  (forall ( (A Int) (v_1 Int) ) 
    (=>
      (and
        (and (not (<= A (- 1))) (not (>= A 2)) (= v_1 A))
      )
      (REC__f A v_1)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (and (not (>= A 2)) (<= A (- 1)) (= B 0))
      )
      (REC__f A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (REC_f_ D C)
        (and (= A (+ 1 D)) (>= A 1) (<= C (- 2)) (= B 0))
      )
      (REC_f_ A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (REC_f_ D C)
        (and (= C (+ (- 1) B)) (>= A 1) (not (<= C (- 2))) (= A (+ 1 D)))
      )
      (REC_f_ A B)
    )
  )
)
(assert
  (forall ( (A Int) (v_1 Int) ) 
    (=>
      (and
        (and (not (<= A (- 1))) (not (>= A 1)) (= v_1 A))
      )
      (REC_f_ A v_1)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (and (not (>= A 1)) (<= A (- 1)) (= B 0))
      )
      (REC_f_ A B)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (REC_f_ F E)
        (and (= A (+ 1 F))
     (= D 0)
     (>= A 1)
     (not (>= C 2))
     (<= C (- 1))
     (<= E (- 2))
     (= B 0))
      )
      (REC_f_f A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (REC_f_ F E)
        (and (= D 0)
     (= E (+ (- 1) B))
     (>= A 1)
     (not (>= C 2))
     (<= C (- 1))
     (not (<= E (- 2)))
     (= A (+ 1 F)))
      )
      (REC_f_f A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (v_5 Int) ) 
    (=>
      (and
        (REC_f_ E D)
        (and (= B 0)
     (>= A 1)
     (not (>= C 2))
     (not (<= C (- 1)))
     (<= D (- 2))
     (= A (+ 1 E))
     (= v_5 C))
      )
      (REC_f_f A B C v_5)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (v_5 Int) ) 
    (=>
      (and
        (REC_f_ E D)
        (and (= D (+ (- 1) B))
     (>= A 1)
     (not (>= C 2))
     (not (<= C (- 1)))
     (not (<= D (- 2)))
     (= A (+ 1 E))
     (= v_5 C))
      )
      (REC_f_f A B C v_5)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (REC_f_f G F H E)
        (and (= A (+ 1 G))
     (= C (+ 2 H))
     (= E (+ (- 2) D))
     (>= A 1)
     (>= C 2)
     (<= F (- 2))
     (not (<= E (- 3)))
     (= B 0))
      )
      (REC_f_f A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (REC_f_f G E H F)
        (and (= C (+ 2 H))
     (= F (+ (- 2) D))
     (= E (+ (- 1) B))
     (>= A 1)
     (>= C 2)
     (not (<= F (- 3)))
     (not (<= E (- 2)))
     (= A (+ 1 G)))
      )
      (REC_f_f A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (REC_f_f G E H F)
        (and (= A (+ 1 G))
     (= D 0)
     (= C (+ 2 H))
     (>= A 1)
     (>= C 2)
     (<= F (- 3))
     (<= E (- 2))
     (= B 0))
      )
      (REC_f_f A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (REC_f_f G E H F)
        (and (= D 0)
     (= C (+ 2 H))
     (= E (+ (- 1) B))
     (>= A 1)
     (>= C 2)
     (<= F (- 3))
     (not (<= E (- 2)))
     (= A (+ 1 G)))
      )
      (REC_f_f A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (v_5 Int) ) 
    (=>
      (and
        (REC__f E D)
        (and (= B (+ 2 E))
     (not (>= A 1))
     (>= B 2)
     (not (<= A (- 1)))
     (<= D (- 3))
     (= C 0)
     (= v_5 A))
      )
      (REC_f_f A v_5 B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (v_5 Int) ) 
    (=>
      (and
        (REC__f E D)
        (and (= D (+ (- 2) C))
     (not (>= A 1))
     (>= B 2)
     (not (<= A (- 1)))
     (not (<= D (- 3)))
     (= B (+ 2 E))
     (= v_5 A))
      )
      (REC_f_f A v_5 B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (v_2 Int) (v_3 Int) ) 
    (=>
      (and
        (and (not (>= A 1))
     (not (<= B (- 1)))
     (not (<= A (- 1)))
     (not (>= B 2))
     (= v_2 A)
     (= v_3 B))
      )
      (REC_f_f A v_2 B v_3)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (v_3 Int) ) 
    (=>
      (and
        (and (not (>= A 1))
     (not (>= B 2))
     (not (<= A (- 1)))
     (<= B (- 1))
     (= C 0)
     (= v_3 A))
      )
      (REC_f_f A v_3 B C)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (REC__f F E)
        (and (= D 0)
     (= C (+ 2 F))
     (not (>= A 1))
     (>= C 2)
     (<= A (- 1))
     (<= E (- 3))
     (= B 0))
      )
      (REC_f_f A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (REC__f F E)
        (and (= C (+ 2 F))
     (= E (+ (- 2) D))
     (not (>= A 1))
     (>= C 2)
     (<= A (- 1))
     (not (<= E (- 3)))
     (= B 0))
      )
      (REC_f_f A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (v_3 Int) ) 
    (=>
      (and
        (and (not (>= A 1))
     (not (>= C 2))
     (<= A (- 1))
     (not (<= C (- 1)))
     (= B 0)
     (= v_3 C))
      )
      (REC_f_f A B C v_3)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (and (= D 0) (not (>= A 1)) (not (>= C 2)) (<= A (- 1)) (<= C (- 1)) (= B 0))
      )
      (REC_f_f A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (and (not (= A 0))
     (not (>= B 1))
     (not (>= A 2))
     (<= B (- 1))
     (not (<= A (- 1)))
     (= B A))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (REC__f C A)
        (and (not (= A (- 2)))
     (= D B)
     (>= B 2)
     (not (>= D 1))
     (not (<= A (- 3)))
     (<= D (- 1))
     (= B (+ 2 C)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) ) 
    (=>
      (and
        (and (= A B)
     (not (>= B 2))
     (not (>= A 1))
     (<= B (- 1))
     (not (<= A (- 1)))
     (not (= A 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (REC__f D B)
        (and (= A C)
     (= C (+ 2 D))
     (not (>= A 1))
     (>= C 2)
     (not (<= B (- 3)))
     (not (<= A (- 1)))
     (not (= A (+ 2 B))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (REC__f D B)
        (and (= A C)
     (= C (+ 2 D))
     (not (>= A 1))
     (>= C 2)
     (<= B (- 3))
     (not (<= A (- 1)))
     (not (= A 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (REC_f_f D A F B)
        (and (= C (+ 1 D))
     (= C E)
     (= E (+ 2 F))
     (>= C 1)
     (>= E 2)
     (<= B (- 3))
     (not (<= A (- 2)))
     (not (= A (- 1))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (REC_f_f D A F B)
        (and (= C (+ 1 D))
     (= C E)
     (= E (+ 2 F))
     (>= C 1)
     (>= E 2)
     (not (<= B (- 3)))
     (not (<= A (- 2)))
     (not (= A (+ 1 B))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) 
    (=>
      (and
        (REC_f_f D B F A)
        (and (= C (+ 1 D))
     (= C E)
     (= E (+ 2 F))
     (>= C 1)
     (>= E 2)
     (<= B (- 2))
     (not (<= A (- 3)))
     (not (= A (- 2))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (REC_f_ D A)
        (and (= C (+ 1 D))
     (= C B)
     (not (>= B 2))
     (>= C 1)
     (not (<= B (- 1)))
     (not (<= A (- 2)))
     (not (= A (+ (- 1) B))))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (REC_f_ D B)
        (and (= C (+ 1 D))
     (= C A)
     (not (>= A 2))
     (>= C 1)
     (<= B (- 2))
     (not (<= A (- 1)))
     (not (= A 0)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (REC_f_ C A)
        (and (= B D)
     (not (= A (- 1)))
     (>= B 1)
     (not (>= D 2))
     (not (<= A (- 2)))
     (<= D (- 1))
     (= B (+ 1 C)))
      )
      CHC_COMP_FALSE
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) ) 
    (=>
      (and
        CHC_COMP_FALSE
      )
      false
    )
  )
)

(check-sat)
(exit)

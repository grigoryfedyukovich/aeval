(declare-rel inv (Int Int))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)
(declare-var x6 Int)
(declare-var x7 Int)
(declare-var x8 Int)
(declare-var x9 Int)

(declare-rel fail ())

(rule (=> (and (= x1 0) (= x3 100)) (inv x1 x3)))

(rule (=> 
    (and 
	(inv x1 x3)
        (= x2 (+ x1 1))
        (ite (ite (> x2 0) (> x3 0) (= x3 5)) 
             (= x4 x2) (= x4 x3))
    )
    (inv x2 x4)
  )
)

(rule (=> (and (inv x1 x3) (not (> x3 0) )) fail))

(query fail :print-certificate true)


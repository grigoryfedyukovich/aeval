(declare-rel inv (Int Int))
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)
(declare-var x6 Int)

(declare-rel fail ())

(rule (=> (and (>= x1 0) (<= x1 2) (>= x3 0) (<= x3 2)) (inv x1 x3)))

(rule (=> 
    (and 
	(inv x1 x3)
	(= x2 (+ x1 2))
	(= x4 (+ x3 2))
    )
    (inv x2 x4)
  )
)


(rule (=> (and (inv x1 x3) (= x1 4) (= x3 0)) fail))


(query fail :print-certificate true)


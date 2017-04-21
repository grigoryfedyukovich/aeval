(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x2 Int)
(declare-var y Int)
(declare-var y2 Int)

(declare-rel fail ())


(rule (=>
    (and (= x 0) (= y 50)) (inv x y)
  )
)


(rule (=> 
    (and 
	(inv x y)
	(< x 100)
        (= x2 (+ x 1))
	(ite (> x2 50) (= y2 (+ y 1)) (= y2 y))
    )
    (inv x2 y2)
  )
)

(rule (=> (and (> x 50) (inv x y) (not (= y x))) fail))


(query fail :print-certificate true)


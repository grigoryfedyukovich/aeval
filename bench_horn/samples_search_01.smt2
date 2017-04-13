(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var i Int)
(declare-var i1 Int)

(declare-rel fail ())

(rule (=>
    (and (= x 32) (= i 25)) (inv x i)
  )
)

(rule (=> 
    (and 
	(inv x i)
	(= i1 (+ i 112))
	(= x1 (+ x i1))
    )
    (inv x1 i1)
  )
)


(rule (=> (and (inv x i) (not (>= x 0))) fail))


(query fail :print-certificate true)


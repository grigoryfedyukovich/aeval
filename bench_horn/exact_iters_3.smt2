(declare-rel inv (Int Int))
(declare-var i1 Int)
(declare-var i2 Int)
(declare-var j1 Int)
(declare-var j2 Int)

(declare-rel fail ())

(rule (=> (and (= i1 0) (= j1 10000)) (inv i1 j1)))

(rule (=> 
    (and 
	(inv i1 j1)
	(= i2 (+ i1 2))
	(= j2 (- j1 1))
    )
    (inv i2 j2)
  )
)


(rule (=> (and (inv i1 j1) (= i1 4000) (not (= j1 8000)) ) fail))


(query fail :print-certificate true)


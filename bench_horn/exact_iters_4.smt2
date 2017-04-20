(declare-rel inv (Int Int Int))
(declare-var i1 Int)
(declare-var i2 Int)
(declare-var j1 Int)
(declare-var j2 Int)
(declare-var k1 Int)
(declare-var k2 Int)

(declare-rel fail ())

(rule (=> (and (= i1 0) (= j1 10) (= k1 0)) (inv i1 j1 k1)))

(rule (=> 
    (and 
	(inv i1 j1 k1)
	(= i2 (+ i1 1))
	(= j2 (- j1 3))
	(= k2 (+ k1 2))
    )
    (inv i2 j2 k2)
  )
)


(rule (=> (and (inv i1 j1 k1) (= (+ i1 k1) 6) (not (= j1 4)) ) fail))


(query fail :print-certificate true)


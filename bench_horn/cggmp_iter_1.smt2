(declare-rel inv (Int Int))
(declare-var i1 Int)
(declare-var i2 Int)
(declare-var j1 Int)
(declare-var j2 Int)

(declare-rel fail ())

(rule (=> (and (= i1 1) (= j1 2)) (inv i1 j1)))

(rule (=> 
    (and 
	(inv i1 j1)
	(>= j1 i1)
	(= i2 (+ i1 2))
	(= j2 (- j1 1))
    )
    (inv i2 j2)
  )
)


(rule (=> (and (inv i1 j1) (< j1 i1) (not (= j1 1)) ) fail))


(query fail :print-certificate true)


(declare-rel inv (Int Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var nondet1 Int)
(declare-var nondet2 Int)

(declare-rel fail ())

(rule (=>
    (and (= x 0) (= y 0) (= i 0) (= j 0)) (inv x y i j)
  )
)

(rule (=> 
    (and 
	(inv x y i j)
	(= i1 (+ i nondet1))
        (= j1 (+ j nondet2))
	(= x1 (+ x nondet1))
        (= y1 (+ y nondet2))
    )
    (inv x1 y1 i1 j1)
  )
)


(rule (=> (and (inv x y i j) (>= i j) (not (>= x y))) fail))


(query fail :print-certificate true)


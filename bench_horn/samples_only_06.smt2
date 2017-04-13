(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var i Int)
(declare-var i1 Int)

(declare-rel fail ())

(rule (=>
    (and (= x 0) (= y 0) (= i 0)) (inv x y i)
  )
)

(rule (=> 
    (and 
	(inv x y i)
	(= i1 (+ i 1))
	(= x1 (+ x i1))
        (= y1 (- y i1))
    )
    (inv x1 y1 i1)
  )
)

;(= 0 (- x (+ y (- 8 i 7)))) - not needed actually, just to test


(rule (=> (and (inv x y i) (= 0 (- x (+ y (- 8 i 7)))) (not (= x (- y)))) fail))


(query fail :print-certificate true)


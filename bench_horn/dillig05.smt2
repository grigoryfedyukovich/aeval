(declare-rel itp (Int Int Int Int))
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)
(declare-var x6 Int)
(declare-var x7 Int)
(declare-var x8 Int)
(declare-var tmp Int)

(declare-rel fail ())

(rule (=> (and (= x1 0) (= x3 0) (= x5 0) (= x7 0)) (itp x1 x3 x5 x7)
  )
)

(rule (=> 
    (and 
	(itp x1 x3 x5 x7)
        (= x2 (+ x1 1))
        (= x4 (+ x3 1))
        (= x6 (+ x5 x2))
        (= tmp (+ x7 x4))
	(or (= x8 tmp) (= x8 (+ tmp 1)))
    )
    (itp x2 x4 x6 x8)
  )
)


(rule (=> (and (itp x1 x3 x5 x7) 
   (not (> x7 (- x5 1))
   )) fail))


(query fail :print-certificate true)


(declare-rel itp (Int Int Int))
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)
(declare-var x6 Int)

(declare-rel fail ())

(rule (=> (and (= x1 1) (= x3 1) (= x5 1)) (itp x1 x3 x5)
  )
)

(rule (=> 
    (and 
	(itp x1 x3 x5)
	(= x2 (+ x1 1))
	(= x4 (+ x1 x1))
        (= x6 (+ x1 x1 x1))
    )
    (itp x2 x4 x6)
  )
)


(rule (=> (and (itp x1 x3 x5) 
   (not 
     (or 
       (> (- x5 x3) 500)
       (< x1 1000)
     )
   )) fail))


(query fail :print-certificate true)


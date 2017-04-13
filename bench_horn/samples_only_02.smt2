(declare-rel itp (Int Int Int Int Int))
(declare-var x0 Int)
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)
(declare-var x6 Int)
(declare-var x7 Int)
(declare-var x8 Int)
(declare-var x9 Int)

(declare-rel fail ())

(rule (=>
    (and (= x1 2) (= x2 2) (= x3 2) (= x4 2) (= x5 2)) (itp x1 x2 x3 x4 x5)
  )
)

(rule (=> 
    (and 
	(itp x1 x3 x5 x7 x9)
	(= x2 (+ x1 1))
	(= x4 (+ x3 1))
	(= x6 (+ x5 1))
	(= x8 (+ x7 1))
	(= x0 (+ x9 1))
    )
    (itp x2 x4 x6 x8 x0)
  )
)


(rule (=> (and (itp x1 x3 x5 x7 x9) 
   (not 
     (and 
       (> x1 0)
       (> x3 0)
       (> x5 0)
       (> x7 0)
       (> x9 0)
     )
   )) fail))


(query fail :print-certificate true)


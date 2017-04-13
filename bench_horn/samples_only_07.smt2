(declare-rel itp (Int))
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

(rule (=> (= x3 0) (itp x3)
  )
)

(rule (=> 
    (and 
	(itp x3)
        (= x4 (ite (= x3 10) 0 (+ x3 1)))
    )
    (itp x4)
  )
)


(rule (=> (and (itp x3) 
   (not 
     (<= x3 10)
   )) fail))


(query fail :print-certificate true)


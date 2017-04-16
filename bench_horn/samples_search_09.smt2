(declare-rel inv (Int Int ))
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-rel fail ())

(rule (=> (= x1 1) (inv x1 x3)))

(rule (=> 
    (and 
	(inv x1 x3)
	(= x2 (+ x1 x1))
	(= x4 x1)
    )
    (inv x2 x4)
  )
)


(rule (=> (and (inv x1 x3) 
   (not 
     (or 
       (= x1 (- (* 3 x3) x3))
       (= x1 1)
     )
   )) fail))


(query fail :print-certificate true)


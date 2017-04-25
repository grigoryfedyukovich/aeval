(declare-rel inv (Int Int Int))
(declare-var a Int)
(declare-var c1 Int)
(declare-var c2 Int)
(declare-var d1 Int)
(declare-var d2 Int)

(declare-rel fail ())

(rule (=> (and (> a 0) (= c1 0) (= d1 0)) (inv a c1 d1)))

(rule (=> 
    (and 
	(inv a c1 d1)
        (= d2 (+ d1 1))
	(= c2 (+ c1 a))
    )
    (inv a c2 d2)
  )
)


(rule (=> (and (inv a c1 d1) (not (= c1 (* a d1)))) fail))


(query fail :print-certificate true)


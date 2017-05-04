(declare-rel inv (Int Int))
(declare-var a Int)
(declare-var a2 Int)
(declare-var b Int)
(declare-var b2 Int)

(declare-rel fail ())

(rule (=> (and (= a 1) (= b 1)) (inv a b)))

(rule (=> 
    (and 
	(inv a b)
        (= a2 (+ a 1))
	(= b2 (* b a))
    )
    (inv a2 b2)
  )
)


(rule (=> (and (inv a b) (not (> b 0))) fail))


(query fail :print-certificate true)


(declare-rel inv (Int Int))
(declare-var a Int)
(declare-var b Int)
(declare-var b2 Int)

(declare-rel fail ())

(rule (=> (and (> a 0) (= b 1)) (inv a b)))

(rule (=> 
    (and 
	(inv a b)
	(= b2 (* b a))
    )
    (inv a b2)
  )
)


(rule (=> (and (inv a b) (not (> b 0))) fail))


(query fail :print-certificate true)


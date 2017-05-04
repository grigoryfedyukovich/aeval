(declare-rel inv (Int Int))
(declare-var a Int)
(declare-var b Int)
(declare-var a1 Int)

(declare-rel fail ())

(rule (=> (and (> b 0) (= b a)) (inv a b)))

(rule (=> 
    (and 
	(inv a b)
        (= a1 (+ a b))
    )
    (inv a1 b)
  )
)

(rule (=> (and (inv a b) (not (= 0 (mod a b)))) fail))

(query fail :print-certificate true)
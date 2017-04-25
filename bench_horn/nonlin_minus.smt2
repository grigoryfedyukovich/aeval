(declare-rel inv (Int Int Int))
(declare-var a Int)
(declare-var a2 Int)
(declare-var n Int)
(declare-var n2 Int)
(declare-var b Int)

(declare-rel fail ())

(rule (=> (and (> a 0) (> b 0) (= n (* a b))) (inv a b n)))

(rule (=> 
    (and 
	(inv a b n)
        (= n2 (- n b))
        (= a2 (- a 1))
    )
    (inv a2 b n2)
  )
)


(rule (=> (and (inv a b n) (= n 0) (not (= a 0))) fail))


(query fail :print-certificate true)


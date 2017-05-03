(declare-rel inv (Int Int Int))
(declare-var a Int)
(declare-var a1 Int)
(declare-var b Int)
(declare-var c Int)
(declare-var c1 Int)

(declare-rel fail ())

(rule (=> (and (> b 0) (= b a) (= c 1)) (inv a b c)))

(rule (=> 
    (and 
	(inv a b c)
        (= a1 (+ a b))
        (= c1 (+ 1 c))
    )
    (inv a1 b c1)
  )
)

(rule (=> (and (inv a b c) (not (= c (/ a b)))) fail))

(query fail :print-certificate true)
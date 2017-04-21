(declare-rel inv (Int Int Int Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var k Int)
(declare-var k1 Int)
(declare-var l Int)
(declare-var l1 Int)
(declare-var m Int)
(declare-var m1 Int)

(declare-rel fail ())

(rule (=> (and (= x 1) (= i 1) (= j 1) (= k 1) (= l 1) (= m 1)) (inv x i j k l m)))

(rule (=> 
    (and 
	(inv x i j k l m)
	(= x1 (+ x i j k l m))
	(= i1 (+ x i j k l m))
        (= j1 (+ x i j k l m))
	(= k1 (+ x i j k l m))
	(= l1 (+ x i j k l m))
        (= m1 (+ x i j k l m))
    )
    (inv x1 i1 j1 k1 l1 m1)
  )
)


(rule (=> (and (inv x i j k l m) (not (>= x 1))) fail))


(query fail :print-certificate true)


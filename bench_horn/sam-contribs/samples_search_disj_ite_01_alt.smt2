(declare-rel itp (Int Int))
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
(declare-var c1 Int)
(declare-var c2 Int)

(declare-rel fail ())


(rule (=>
    (and (= x1 0) (= x3 100)) (itp x1 x3)
  )
)

(rule (=>
    (and
	(itp x1 x3)
        (= x2 (+ x1 1))
        (or (and (> x2 0) (= c1 1))
            (and (<= x2 0) (= c1 0)))
        (or (and (> x3 10) (= c2 -1))
            (and (<= x3 10) (= c2 x3)))
        (= x4 (+ c1 c2))

    )
    (itp x2 x4)
  )
)


(rule (=> (and (itp x1 x3) (> x1 10)
   (not
     (< x3 x1)
   )) fail))


(query fail :print-certificate true)

(declare-rel itp (Int Int Int Int Int))
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)
(declare-var x6 Int)
(declare-var x7 Int)
(declare-var x8 Int)
(declare-var x9 Int)
(declare-var x0 Int)
(declare-var y1 Int)
(declare-var y3 Int)
(declare-var y5 Int)
(declare-var y7 Int)
(declare-var y9 Int)

(declare-rel fail ())

(rule (=> (and (= x1 0) (= x3 0) (= x5 0) (= x7 0) (= x9 0)) (itp x1 x3 x5 x7 x9)))

(rule (=>
    (and
    	(itp x1 x3 x5 x7 x9)
      (or (and (and (= x2 y1) (= x4 y3) (= x6 y5) (= x8 y7) (= x0 y9))
               (and (<= 0 y1) (<= y1 (+ y7 1)) (= y3 y5) (or (<= y3 -1) (<= y7 (+ y3 2))) (= y9 0)))
          (and (not (and (<= 0 y1) (<= y1 (+ y7 1)) (= y3 y5) (or (<= y3 -1) (<= y7 (+ y3 2))) (= y9 0)))
               (and (= x2 x1) (= x4 x3) (= x6 x5) (= x8 x7) (= x0 x9)) ))
    )
    (itp x2 x4 x6 x8 x0)
  )
)


(rule (=> (and (itp x1 x3 x5 x7 x9)
               (not (and (<= 0 x1) (<= x1 (+ x7 1)) (= x3 x5) (or (<= x3 -1) (<= x7 (+ x3 2))) (= x9 0)))
          ) fail))

(query fail :print-certificate true)

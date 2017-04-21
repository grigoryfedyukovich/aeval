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

(define-fun tmp ((x1 Int) (x2 Int) (x3 Int) (x4 Int) (x5 Int)) Bool
  (and (<= 0 x1) (<= x1 (+ x4 1)) (= x2 x3) (or (<= x2 -1) (<= x4 (+ x2 2))) (= x5 0)))

(rule (=> (and (= x1 0) (= x3 0) (= x5 0) (= x7 0) (= x9 0)) (itp x1 x3 x5 x7 x9)))

(rule (=> 
    (and 
	(itp x1 x3 x5 x7 x9)
        (ite (tmp y1 y3 y5 y7 y9) 
            (and (= x2 y1) (= x4 y3) (= x6 y5) (= x8 y7) (= x0 y9)) 
            (and (= x2 x1) (= x4 x3) (= x6 x5) (= x8 x7) (= x0 x9)))
    )
    (itp x2 x4 x6 x8 x0)
  )
)


(rule (=> (and (itp x1 x3 x5 x7 x9) (not (tmp x1 x3 x5 x7 x9))) fail))

(query fail :print-certificate true)


(declare-rel itp (Int Int Int Int))
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)
(declare-var x6 Int)
(declare-var x7 Int)
(declare-var x8 Int)
(declare-var y1 Int)
(declare-var y3 Int)
(declare-var y5 Int)
(declare-var y7 Int)

(declare-rel fail ())

(define-fun tmp ((x1 Int) (x2 Int) (x3 Int) (x4 Int)) Bool
  (and (<= x1 0) (>= x1 (+ x4 1)) (= x2 x3) (or (>= x4 0) (<= x4 x3))))

(rule (=> (and (= x1 0) (= x3 0) (= x5 0) (= x7 -1)) (itp x1 x3 x5 x7)))

(rule (=> 
    (and 
	(itp x1 x3 x5 x7)
        (ite (tmp y1 y3 y5 y7) 
            (and (= x2 y1) (= x4 y3) (= x6 y5) (= x8 y7)) 
            (and (= x2 x1) (= x4 x3) (= x6 x5) (= x8 x7)))
    )
    (itp x2 x4 x6 x8)
  )
)


(rule (=> (and (itp x1 x3 x5 x7) (not (tmp x1 x3 x5 x7))) fail))

(query fail :print-certificate true)


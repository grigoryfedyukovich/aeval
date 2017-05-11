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

;(define-fun tmp ((y1 Int) (y3 Int) (y5 Int) (y7 Int)) Bool
;  (and (<= y1 0) (>= y1 (+ y7 1)) (= y3 y5) (or (>= y7 0) (<= y7 y5))))

(rule (=> (and (= x1 0) (= x3 0) (= x5 0) (= x7 -1)) (itp x1 x3 x5 x7)))

(rule (=>
    (and
    	(itp x1 x3 x5 x7)
      (or
        (and (and (<= y1 0) (>= y1 (+ y7 1)) (= y3 y5) (or (>= y7 0) (<= y7 y5))) (and (= x2 y1) (= x4 y3) (= x6 y5) (= x8 y7)))
        (and (not (and (<= y1 0) (>= y1 (+ y7 1)) (= y3 y5) (or (>= y7 0) (<= y7 y5))))  (and (= x2 x1) (= x4 x3) (= x6 x5) (= x8 x7)))
      )
    )
    (itp x2 x4 x6 x8)
  )
)


(rule (=> (and (itp x1 x3 x5 x7) (not (and (<= x1 0) (>= x1 (+ x7 1)) (= x3 x5) (or (>= x7 0) (<= x7 x5))))) fail))

(query fail :print-certificate true)

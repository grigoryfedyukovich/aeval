(declare-var x0 Int)
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-rel itp (Int Int Int))
(declare-rel fail ())

(rule (=>
  (and
    (itp x0 x2 x1)
    (or
      (<= 99 (+ x2 x1))
      (not (>= (+ x2 x1) 0))
    )
    (not (= (mod (+ (mod x2 2) (mod x1 2)) 2) x0))
  ) fail))

(rule (=>
  (and
    (= x0 (ite (= x1 0) 1 2))
    (= x1 (mod x2 2))
  )
  (itp x1 x0 x0)))

(rule (=>
  (and
    (itp x1 x0 x3)
    (>= x2 0)
    (not (<= 99 x2))
    (= x2 (+ x0 x3))
  )
  (itp x1 x0 x2)))

(query fail :print-certificate true)

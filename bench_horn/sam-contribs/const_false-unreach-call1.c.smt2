(declare-var x Int)
(declare-var x_ Int)
(declare-var y Int)
(declare-var y_ Int)
(declare-rel itp (Int Int))
(declare-rel fail ())

(rule (=>
  ; (and (= y 1) (= x 0))
  (and (= y 0) (= x 1))
  (itp y x)))

(rule (=>
  (and
    (itp y_ x_)
    (>= y_ 0)  ; unsigned
    (< y_ 1024)  ; (not (<= 1024 (:var 1)))
    (= y (+ 1 y_))
    (= x 0)
  )
  (itp y x)))

(rule (=>
  (and
    (itp y_ x_)
    (>= y_ 0)  ; unsigned
    (>= y_ 1024)
    (not (= x_ 1))
  )
  fail))

(query fail :print-certificate true)

(declare-var x Int)
(declare-var x_ Int)
(declare-var y Int)
(declare-var y_ Int)
(declare-rel itp (Int Int))
(declare-rel fail ())

(rule (=> (and (= x 1) (= y 2))
          (itp x y)))

(rule (=>
  (and
    (itp x_ y_)
    (>= x 0)  ; unsigned
    (>= y 0)  ; unsigned
    (< x_ 6)
    (= x (+ 1 x_))
    (= y (* 2 y_))
  )
  (itp x y)))

(rule (=> (and (itp x y) (= y 64))
          fail))

(query fail :print-certificate true)

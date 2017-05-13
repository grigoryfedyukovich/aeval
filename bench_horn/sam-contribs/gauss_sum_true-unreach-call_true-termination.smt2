; TODO: check this one; may have error
(set-option :verbose 2)

(declare-var n Int)
(declare-var sum Int)
(declare-var sum_ Int)
(declare-var i Int)
(declare-var i_ Int)
(declare-var LRG Int)
(declare-rel itp (Int Int Int))
(declare-rel fail ())

(rule (=>
  (and
    (<= 1 n)
    (<= n 1000)
    (= sum 0)
    (= i 1)
  )
  (itp n sum i)
))

(rule (=>
  (and
    (itp n sum_ i_)
    (<= i_ n)
    (= sum (+ i_ sum_))
    (= i (+ 1 i_))
  )
  (itp n sum i)
))

(rule (=>
  (and
    (itp n sum i)
    (not (<= i n))  ; stop cond
    (not (= (* 2 sum) (* n (+ n 1))))
  )
  fail
))

(query fail :print-certificate true)

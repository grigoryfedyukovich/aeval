(declare-var i Int)
(declare-var i_ Int)
(declare-var LRG Int)
(declare-rel itp (Int Int))
(declare-rel fail ())

(rule (=>
  (and
    (= i 0)
    (not (= i LRG))
  )
  (itp i LRG)
))

(rule (=>
  (and
    (itp i_ LRG)
    (= i (+ 1 i_))
    (not (= i LRG))
  )
  (itp i LRG)
))

(rule (=>
  (and
    (> i LRG)
    (itp i LRG)
    (> LRG 10000)  ; assume LARGE_INT is actually large
  )
  fail
))

(query fail :print-certificate true)

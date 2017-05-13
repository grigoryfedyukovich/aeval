(declare-var i Int)
(declare-var i_ Int)
(declare-var k Int)
(declare-var k_ Int)
(declare-var j Int)
(declare-var LRG Int)
(declare-rel itp (Int Int Int))
(declare-rel fail ())

(rule (=>
  (and
    (= i 0)
    (= k 0)
    (< i LRG)
  )
  (itp i k LRG)
))

(rule (=>
  (and
    (itp i_ k_ LRG)
    (not (<= LRG i))
    (not (<= LRG (- i i_)))  ; follows from j{1,LRG}
    (>= i (+ i_ 1))  ; follows from j{1,LRG}
    (= k (+ 1 k_))
  )
  (itp i k LRG)
))

(rule (=>
  (and
    (itp i k LRG)
    (< LRG (+ k 1))  ; assert
    (<= 1 j)
    (< j LRG)
    (<= LRG (+ j i))
    (= LRG 256)  ; LARGE_INT is large and a power of 2
  )
  fail
))

(query fail :print-certificate true)

;here '3*CC' is 'CELLCOUNT' of original program

(declare-var CC Int)
(declare-var i Int)
(declare-var i1 Int)
(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var a2 (Array Int Int))
(declare-var a3 (Array Int Int))
(declare-var val1 Int)
(declare-var val2 Int)
(declare-var val3 Int)
(declare-var minval Int)

(declare-rel inv ((Array Int Int) Int Int Int Int Int Int))
(declare-rel fail ())

(rule (=> (and (> CC 0) (= val1 1) (=  val2 3) (= val3 7) (= i 1))
          (inv a i CC val1 val2 val3 minval)))

(rule (=> (and
           (inv a i CC val1 val2 val3 minval)
           (<= i (* 1 CC))
           (= i1 (+ i 1))
           (= a1 (ite (<= minval val3)
		      (store a (- (* 3 i) 3) val3)
		      (store a (- (* 3 i) 3) 0)))
           (= a2 (ite (<= minval val2)
		      (store a1 (- (* 3 i) 2) val2)
		      (store a1 (- (* 3 i) 2) 0)))
           (= a3 (ite (<= minval val1)
		      (store a2 (- (* 3 i) 1) val1)
		      (store a2 (- (* 3 i) 1) 0))))
          (inv a3 i1 CC val1 val2 val3  minval)))

(rule (=> (and
           (inv a i CC val1 val2 val3 minval)
           (not (<= i (* 1 CC)))
           (<= 0 i1)
           (< i1 (* 3 CC))
           (not (or (<= minval (select a i1)) (= (select a i1) 0))))
          fail))

(query fail)

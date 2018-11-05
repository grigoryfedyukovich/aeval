(declare-var S Int)
(declare-var i Int)
(declare-var i1 Int)
(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))

(declare-rel inv ((Array Int Int) Int Int))
(declare-rel fail ())

(rule (=> (and (<= 1 S) (= i 0)) (inv a i S)))

(rule (=> (and (inv a i S) (< i S) (= (store a i (* i i)) a1) (= i1 (+ i 1))) (inv a1 i1 S)))

(rule (=> (and (inv a i S) (not (< i S)) (<= 0 i1) (< i1 S) (not (= (select a i1) (* i1 i1)))) fail))

(query fail)

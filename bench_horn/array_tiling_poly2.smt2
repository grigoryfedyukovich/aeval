(declare-var S Int)
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))

(declare-rel inv1 ((Array Int Int) Int Int))
(declare-rel inv2 ((Array Int Int) Int Int))
(declare-rel fail ())

(rule (=> (<= 1 S) (inv1 a 0 S)))

(rule (=> (and (inv1 a i S) (< i S) (= (store a i (+ (+ i i) 2)) a1) (= i1 (+ i 1))) (inv1 a1 i1 S)))

(rule (=> (and (not (< i S)) (inv1 a i S) (= i1 0)) (inv2 a i1 S)))

(rule (=> (and (inv2 a i S) (< i S) (= (store a i (- (select a i) 2)) a1) (= i1 (+ i 1))) (inv2 a1 i1 S)))

(rule (=> (and (inv2 a i S) (not (< i S)) (<= 0 i1) (< i1 S) (not (= (select a i1) (+ i1 i1)))) fail))

(query fail)

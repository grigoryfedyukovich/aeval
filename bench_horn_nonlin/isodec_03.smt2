(declare-rel inv4 (Int))
(declare-var x Int)
(declare-var y Int)
(declare-var z Int)

(declare-rel fail ())

(rule (=> false (inv4 x)))

(rule (=> (and (inv4 x) (inv4 y) (inv4 z) (= x (+ y z)) (not (> z (+ x y)))) fail))

(query fail)

(declare-rel inv4 (Int))
(declare-var x Int)
(declare-var y Int)

(declare-rel fail ())

(rule (=> false (inv4 x)))

(rule (=> (and (inv4 x) (inv4 y) (not (< (- (* 5 x) y) 0))) fail))

(query fail)

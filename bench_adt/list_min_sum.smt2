(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun sum (Lst) Int)
(assert (= (sum nil) 0))
(assert (forall ((x Int) (y Lst)) (= (sum (cons x y)) (+ x (sum y)))))

(declare-fun min (Lst) Int)
(assert (= (min nil) 0))
(assert (forall ((x Int) (y Lst)) (= (min (cons x y)) (ite (< (min y) x) (min y) x))))

(assert (not (forall ((x Lst)) (=> (>= (min x) 0) (>= (sum x) 0)))))
(check-sat)

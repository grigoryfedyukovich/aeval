(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun min (Lst) Int)
(assert (= (min nil) 0))
(assert (forall ((x Int) (y Lst)) (= (min (cons x y)) (ite (< (min y) x) (min y) x))))

(declare-fun max (Lst) Int)
(assert (= (max nil) 0))
(assert (forall ((x Int) (y Lst)) (= (max (cons x y)) (ite (> (max y) x) (max y) x))))

(assert (not (forall ((x Lst)) (>= (max x) (min x)))))
(check-sat)

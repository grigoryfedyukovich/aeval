(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Int) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(declare-fun min (Lst) Int)
(assert (= (min nil) 0))
(assert (forall ((x Int) (y Lst)) (= (min (cons x y)) (ite (< (min y) x) (min y) x))))

(assert (not (forall ((x Lst) (y Lst))
  (and (<= (min (append x y)) (min x))
       (<= (min (append x y)) (min y))))))
(check-sat)

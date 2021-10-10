(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Int) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(declare-fun sum (Lst) Int)
(assert (= (sum nil) 0))
(assert (forall ((x Int) (y Lst)) (= (sum (cons x y)) (+ x (sum y)))))

(assert (not (forall ((x Lst) (y Lst)) (= (+ (sum x) (sum y)) (sum (append x y))))))
(check-sat)

(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Int) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(declare-fun len (Lst) Int)
(assert (= (len nil) 0))
(assert (forall ((x Int) (y Lst)) (= (len (cons x y)) (+ 1 (len y)))))

(declare-fun butlast (Lst) Lst)
(assert (= (butlast nil) nil))
(assert (forall ((n Int) (x Lst)) (= (butlast (cons n x)) (ite (= x nil) nil (cons n (butlast x))))))

(assert (not (forall ((x Lst) (n Int)) (= (+ 1 (len (butlast (cons n x)))) (len (cons n x))))))
(check-sat)

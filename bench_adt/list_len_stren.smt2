(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun len (Lst) Int)
(assert (= (len nil) 0))
(assert (forall ((x Int) (y Lst)) (= (len (cons x y)) (+ 1 (len y)))))

(declare-fun lenstr (Lst) Int)
(assert (= (lenstr nil) 0))
(assert (forall ((x Int) (y Lst)) (= (lenstr (cons x y)) (+ (len y) (lenstr y)))))

(assert (not (forall ((x Lst)) (>= (lenstr x) 0))))
(check-sat)

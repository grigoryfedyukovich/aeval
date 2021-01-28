(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))
(declare-datatypes () ((Queue (queue (front Lst) (back Lst)))))

(declare-fun len (Lst) Int)
(assert (= (len nil) 0))
(assert (forall ((x Int) (y Lst)) (= (len (cons x y)) (+ 1 (len y)))))

(declare-fun qlen (Queue) Int)
(assert (forall ((x Lst) (y Lst)) (= (qlen (queue x y)) (+ (len x) (len y)))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Int) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(declare-fun butlast (Lst) Lst)
(assert (= (butlast nil) nil))
(assert (forall ((n Int) (x Lst)) (= (butlast (cons n x))
            (ite (= x nil) nil (cons n (butlast x))))))

(declare-fun qpopback (Queue) Queue)
(assert (forall ((x Lst) (y Lst) (n Int)) (= (qpopback (queue x (cons n y))) (queue x y))))
(assert (forall ((x Lst)) (= (qpopback (queue x nil)) (queue (butlast x) nil))))

(declare-fun isAmortized (Queue) Bool)
(assert (forall ((x Lst) (y Lst)) (= (isAmortized (queue x y)) (<= (len y) (len x)))))

(declare-fun isEmpty (Queue) Bool)
(assert (forall ((x Lst) (y Lst)) (= (isEmpty (queue x y)) (and (= x nil) (= y nil)))))

; extra lemma
(assert (forall ((x Lst) (n Int)) (= (len (butlast (cons n x))) (len x))))

(assert (not (forall ((q Queue) (n Int)) (=> (and (isAmortized q) (not (isEmpty q))) (= (+ 1 (qlen (qpopback q))) (qlen q))))))
(check-sat)

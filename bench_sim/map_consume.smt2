(declare-sort Key)
(declare-sort Value)
(declare-datatypes () ((Pair (pair (key Key) (value Value)))))
(declare-datatypes () ((Lst (cons (head Pair) (tail Lst)) (nil))))

(declare-fun xs () Lst)
(declare-fun xs1 () Lst)
(declare-fun in () Key)
(declare-fun inv () Value)
(declare-fun out () Value)
(declare-fun s  () (Array Key Value))
(declare-fun s1 () (Array Key Value))

(declare-fun R (Lst (Array Key Value)) Bool)

(declare-fun remove (Key Lst) Lst)

(declare-fun empty (Int) Value) ; Int - placeholder

(assert (forall ((s (Array Key Value)) (a Key)) (= (R nil s) (forall ((a Key)) (= (empty 0) (select s a))))))
(assert (forall ((xs Lst) (in Key) (s (Array Key Value)) (_x_2 Value)) (= (R (cons (pair in _x_2) xs) s) (and (R xs (store s in (empty 0))) (= (select s in) _x_2)))))

(assert (forall ((x Key)) (= (remove x nil) nil)))
(assert (forall ((x Key) (y Key) (v Value) (xs Lst)) (= (remove x (cons (pair y v) xs)) (ite (= x y) xs (cons (pair y v) (remove x xs))))))

(assert (R xs s))
(assert (not (R (remove in xs) (store s in (empty 0)))))

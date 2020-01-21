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

(declare-fun set (Key Value Lst) Lst)

(declare-fun empty (Int) Value) ; Int - placeholder

(assert (forall ((s (Array Key Value)) (a Key)) (= (R nil s) (forall ((a Key)) (= (empty 0) (select s a))))))
(assert (forall ((xs Lst) (in Key) (s (Array Key Value)) (_x_2 Value)) (= (R (cons (pair in _x_2) xs) s) (and (R xs (store s in (empty 0))) (= (select s in) _x_2)))))

(assert (forall ((x Key) (v Value)) (= (set x v nil) (cons (pair x v) nil))))
(assert (forall ((x Key) (v Value) (y Key) (z Value) (xs Lst)) (= (set x v (cons (pair y z) xs)) (ite (= x y) (cons (pair x v) xs) (cons (pair y z) (set x v xs))))))

(assert (R xs s))
(assert (not (R (set in inv xs) (store s in inv))))

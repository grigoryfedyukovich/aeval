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

(declare-fun empty (Int) Value) ; Int - placeholder

(declare-fun get (Key Lst) Value)
(assert (forall ((x Key)) (= (get x nil) (empty 0))))
(assert (forall ((x Key) (y Key) (z Value) (xs Lst))
  (= (get x (cons (pair y z) xs)) (ite (= x y) z (get x xs)))))

(assert (forall ((s (Array Key Value)) (a Key)) (= (R nil s) (forall ((a Key)) (= (empty 0) (select s a))))))
(assert (forall ((xs Lst) (in Key) (s (Array Key Value)) (_x_2 Value)) (= (R (cons (pair in _x_2) xs) s) (and (R xs (store s in (get in xs))) (= (select s in) _x_2)))))

; extra

(assert (forall ((xs Lst) (in Key) (s (Array Key Value)))
  (=> (R xs s) (= (select s in) (get in xs)))))

(assert (R xs s))
(assert (not (R (cons (pair in inv) xs) (store s in inv))))

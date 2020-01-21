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

(declare-fun removeall (Key Lst) Lst)
(assert (forall ((x Key)) (= (removeall x nil) nil)))
(assert (forall ((x Key) (y Key) (v Value) (xs Lst))
  (= (removeall x (cons (pair y v) xs)) (ite (= x y) (removeall x xs) (cons (pair y v) (removeall x xs))))))

(assert (forall ((s (Array Key Value)) (a Key)) (= (R nil s) (forall ((a Key)) (= (empty 0) (select s a))))))
(assert (forall ((xs Lst) (in Key) (s (Array Key Value)) (_x_2 Value))
  (= (R (cons (pair in _x_2) xs) s) (and (R xs (store s in (get in xs))) (= (select s in) _x_2)))))

; extra

(assert (forall ((xs Lst) (x Key) (y Key))
  (=> (distinct y x) (= (get x (removeall y xs)) (get x xs)))))

(assert (R xs s))
(assert (not (R (removeall in xs) (store s in (empty 0)))))

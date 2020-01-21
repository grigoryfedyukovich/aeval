(declare-sort Key)
(declare-sort Value)
(declare-datatypes () ((Pair (pair (key Key) (value Value)))))
(declare-datatypes () ((Lst (cons (head Pair) (tail Lst)) (nil))))

(declare-fun empty (Int) Value) ; Int - placeholder

(declare-fun get (Key Lst) Value)
(assert (forall ((x Key)) (= (get x nil) (empty 0))))
(assert (forall ((x Key) (y Key) (z Value) (xs Lst))
  (= (get x (cons (pair y z) xs)) (ite (= x y) z (get x xs)))))

(declare-fun removeall (Key Lst) Lst)
(assert (forall ((x Key)) (= (removeall x nil) nil)))
(assert (forall ((x Key) (y Key) (v Value) (xs Lst))
  (= (removeall x (cons (pair y v) xs)) (ite (= x y) (removeall x xs) (cons (pair y v) (removeall x xs))))))

(assert (not (forall ((xs Lst) (x Key) (y Key))
  (=> (distinct y x) (= (get x (removeall y xs)) (get x xs))))))

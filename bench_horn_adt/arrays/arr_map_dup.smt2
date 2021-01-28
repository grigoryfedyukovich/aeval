(set-logic HORN)
(declare-sort Key)
(declare-sort Value)
(declare-fun empty (Int) Value)

(declare-datatypes () ((Pair (pair (key Key) (value Value)))))
(declare-datatypes () ((Lst (cons (head Pair) (tail Lst)) (nil))))
(declare-fun R (Lst (Array Key Value)) Bool)

(declare-fun get (Key Lst) Value)
(assert (forall ((x Key)) (= (get x nil) (empty 0))))
(assert (forall ((x Key) (y Key) (z Value) (xs Lst))
  (= (get x (cons (pair y z) xs)) (ite (= x y) z (get x xs)))))

(declare-fun removeall (Key Lst) Lst)
(assert (forall ((x Key)) (= (removeall x nil) nil)))
(assert (forall ((x Key) (y Key) (v Value) (xs Lst))
  (= (removeall x (cons (pair y v) xs)) (ite (= x y) (removeall x xs) (cons (pair y v) (removeall x xs))))))

; init
(assert (forall ((s (Array Key Value)) (xs Lst))
  (=> (and (forall ((a Key)) (= (empty 0) (select s a))) (= xs nil)) (R xs s))))

; insert-init
(assert (forall ((s (Array Key Value)) (s1 (Array Key Value)) (xs Lst) (xs1 Lst) (in Key) (v Value))
  (=> (and
    (R xs s)
    (= s1 (store s in v))
    (= xs1 (cons (pair in v) xs)))
  (R xs1 s1))))

; remove-init
(assert (forall ((s (Array Key Value)) (s1 (Array Key Value)) (xs Lst) (xs1 Lst) (in Key))
  (=> (and
    (R xs s)
    (= xs1 (removeall in xs))
    (= s1 (store s in (empty 0))))
  (R xs1 s1))))

; contains-out
(assert (forall ((s (Array Key Value)) (xs Lst) (in Key) (out1 Value) (out2 Value))
  (=> (and
    (R xs s)
    (= out1 (select s in))
    (= out2 (get in xs))
    (not (= out1 out2)))
  false)))

(check-sat)

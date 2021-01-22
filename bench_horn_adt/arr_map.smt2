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

(declare-fun set (Key Value Lst) Lst)
(assert (forall ((x Key) (v Value)) (= (set x v nil) (cons (pair x v) nil))))
(assert (forall ((x Key) (v Value) (y Key) (z Value) (xs Lst))
  (= (set x v (cons (pair y z) xs))
     (ite (= x y) (cons (pair x v) xs) (cons (pair y z) (set x v xs))))))

(declare-fun remove (Key Lst) Lst)
(assert (forall ((x Key)) (= (remove x nil) nil)))
(assert (forall ((x Key) (y Key) (v Value) (xs Lst))
  (= (remove x (cons (pair y v) xs)) (ite (= x y) xs (cons (pair y v) (remove x xs))))))

; init
(assert (forall ((s (Array Key Value)) (xs Lst))
  (=> (and (forall ((a Key)) (= (empty 0) (select s a))) (= xs nil)) (R xs s))))

; insert-init
(assert (forall ((s (Array Key Value)) (s1 (Array Key Value)) (xs Lst) (xs1 Lst) (in Key) (v Value))
  (=> (and
    (R xs s)
    (= s1 (store s in v))
    (= xs1 (set in v xs)))
  (R xs1 s1))))

; remove-init
(assert (forall ((s (Array Key Value)) (s1 (Array Key Value)) (xs Lst) (xs1 Lst) (in Key))
  (=> (and
    (R xs s)
    (= xs1 (remove in xs))
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

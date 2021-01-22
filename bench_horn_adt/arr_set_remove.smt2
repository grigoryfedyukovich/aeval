(set-logic HORN)
(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))
(declare-fun R (Lst (Array Elem Bool)) Bool)

(declare-fun contains (Elem Lst) Bool)
(assert (forall ((x Elem)) (= (contains x nil) false)))
(assert (forall ((x Elem) (y Elem) (xs Lst))
  (= (contains x (cons y xs)) (ite (= x y) true (contains x xs)))))

(declare-fun remove (Elem Lst) Lst)
(assert (forall ((x Elem)) (= (remove x nil) nil)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (remove x (cons y xs)) (ite (= x y) xs (cons y (remove x xs))))))

; init
(assert (forall ((s (Array Elem Bool)) (xs Lst))
  (=> (and (forall ((a Elem)) (not (select s a))) (= xs nil)) (R xs s))))

; insert-init
(assert (forall ((s (Array Elem Bool)) (s1 (Array Elem Bool)) (xs Lst) (xs1 Lst) (in Elem))
  (=> (and
    (R xs s)
    (= s1 (store s in true))
    (= xs1 (ite (contains in xs) xs (cons in xs))))
  (R xs1 s1))))

; remove-init
(assert (forall ((s (Array Elem Bool)) (s1 (Array Elem Bool)) (xs Lst) (xs1 Lst) (in Elem))
  (=> (and
    (R xs s)
    (= xs1 (remove in xs))
    (= s1 (store s in false)))
  (R xs1 s1))))

; contains-out
(assert (forall ((s (Array Elem Bool)) (xs Lst) (in Elem) (out1 Bool) (out2 Bool))
  (=> (and
    (R xs s)
    (= out1 (select s in))
    (= out2 (contains in xs))
    (not (= out1 out2)))
  false)))

(check-sat)

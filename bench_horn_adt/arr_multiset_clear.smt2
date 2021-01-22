(set-logic HORN)
(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))
(declare-fun R (Lst (Array Elem Int)) Bool)

(declare-fun num (Elem Lst) Int)
(assert (forall ((x Elem)) (= (num x nil) 0)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (num x (cons y xs)) (ite (= x y) (+ 1 (num x xs)) (num x xs)))))

(declare-fun removeall (Elem Lst) Lst)
(assert (forall ((x Elem)) (= (removeall x nil) nil)))
(assert (forall ((x Elem) (y Elem) (xs Lst))
  (= (removeall x (cons y xs)) (ite (= x y) (removeall x xs) (cons y (removeall x xs))))))

; init
(assert (forall ((s (Array Elem Int)) (xs Lst))
  (=> (and (forall ((a Elem)) (= (select s a) 0)) (= xs nil)) (R xs s))))

; insert-init
(assert (forall ((s (Array Elem Int)) (s1 (Array Elem Int)) (xs Lst) (xs1 Lst) (in Elem))
  (=> (and
    (R xs s)
    (= s1 (store s in (+ 1 (select s in))))
    (= xs1 (cons in xs)))
  (R xs1 s1))))

; remove-init
(assert (forall ((s (Array Elem Int)) (s1 (Array Elem Int)) (xs Lst) (xs1 Lst) (in Elem))
  (=> (and
    (R xs s)
    (= xs1 (removeall in xs))
    (= s1 (store s in 0)))
  (R xs1 s1))))

; contains-out
(assert (forall ((s (Array Elem Int)) (xs Lst) (in Elem) (out1 Int) (out2 Int))
  (=> (and
    (R xs s)
    (= out1 (select s in))
    (= out2 (num in xs))
    (not (= out1 out2)))
  false)))

(check-sat)

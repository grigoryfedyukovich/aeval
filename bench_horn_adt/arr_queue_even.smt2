(set-logic HORN)
(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))
(declare-fun R (Lst (Array Int Elem) Int Int) Bool)

(declare-fun allbutlast (Lst) Lst)
(assert (forall ((x Elem)) (= (allbutlast (cons x nil)) nil)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (allbutlast (cons x (cons y xs))) (cons x (allbutlast (cons y xs))))))

(declare-fun last (Lst) Elem)
(assert (forall ((x Elem)) (= (last (cons x nil)) x)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (last (cons x (cons y xs))) (last (cons y xs)))))

; init
(assert (forall ((xs Lst) (a (Array Int Elem)) (m Int) (n Int))
  (=> (and (= n m) (= xs nil)) (R xs a m n))))

; enqueue-init
(assert (forall ((xs Lst) (xs1 Lst) (a (Array Int Elem)) (a1 (Array Int Elem)) (m Int) (n Int) (m1 Int) (n1 Int) (in Elem))
  (=> (and
    (R xs a m n)
    (= a1 (store a n in))
    (= n1 (+ n 2))
    (= m1 m)
    (= xs1 (cons in xs)))
  (R xs1 a1 m1 n1))))

; dequeue-init
(assert (forall ((xs Lst) (xs1 Lst) (a (Array Int Elem)) (a1 (Array Int Elem)) (m Int) (n Int) (m1 Int) (n1 Int) (out1 Elem) (out2 Elem))
  (=> (and
    (R xs a m n)
    (< m n)
    (= m1 (+ m 2))
    (= n1 n)
    (= a1 a)
    (= out1 (select a m))
    (distinct xs nil)
    (= xs1 (allbutlast xs))
    (= out2 (last xs)))
  (R xs1 a1 m1 n1))))

; dequeue-app-1
(assert (forall ((xs Lst) (xs1 Lst) (a (Array Int Elem)) (a1 (Array Int Elem)) (m Int) (n Int) (m1 Int) (n1 Int) (out1 Elem) (out2 Elem))
  (=> (and
    (R xs a m n)
    (< m n)
    (= xs nil))
  false)))

; dequeue-app-2
(assert (forall ((xs Lst) (xs1 Lst) (a (Array Int Elem)) (a1 (Array Int Elem)) (m Int) (n Int) (m1 Int) (n1 Int) (out1 Elem) (out2 Elem))
  (=> (and
    (R xs a m n)
    (not (= xs nil))
    (not (< m n)))
  false)))

; dequeue-out
(assert (forall ((xs Lst) (xs1 Lst) (a (Array Int Elem)) (a1 (Array Int Elem)) (m Int) (n Int) (m1 Int) (n1 Int) (out1 Elem) (out2 Elem))
  (=> (and
    (R xs a m n)
    (< m n)
    (= m1 (+ m 2))
    (= n1 n)
    (= a1 a)
    (= out1 (select a m))
    (distinct xs nil)
    (= xs1 (allbutlast xs))
    (= out2 (last xs))
    (not (= out1 out2)))
  false)))

(check-sat)

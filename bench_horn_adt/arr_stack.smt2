(set-logic HORN)
(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))
(declare-fun R (Lst (Array Int Elem) Int) Bool)

; init
(assert (forall ((xs Lst) (a (Array Int Elem)) (n Int))
  (=> (and (= n 0) (= xs nil)) (R xs a n))))

; push-init
(assert (forall ((xs Lst) (xs1 Lst) (a (Array Int Elem)) (a1 (Array Int Elem)) (n Int) (n1 Int) (in Elem))
  (=> (and
    (R xs a n)
    (= a1 (store a n in))
    (= n1 (+ n 1))
    (= xs1 (cons in xs)))
  (R xs1 a1 n1))))

; pop-init
(assert (forall ((xs Lst) (xs1 Lst) (a (Array Int Elem)) (a1 (Array Int Elem)) (n Int) (n1 Int) (out1 Elem) (out2 Elem))
  (=> (and
    (R xs a n)
    (> n 0)
    (= n1 (- n 1))
    (= a1 a)
    (= out1 (select a n1))
    (not (= xs nil))
    (= xs (cons out2 xs1)))
  (R xs1 a1 n1))))

; pop-app-1
(assert (forall ((xs Lst) (xs1 Lst) (a (Array Int Elem)) (a1 (Array Int Elem)) (n Int) (n1 Int) (out1 Elem) (out2 Elem))
  (=> (and
    (R xs a n)
    (> n 0)
    (= xs nil))
  false)))

; pop-app-2
(assert (forall ((xs Lst) (xs1 Lst) (a (Array Int Elem)) (a1 (Array Int Elem)) (n Int) (n1 Int) (out1 Elem) (out2 Elem))
  (=> (and
    (R xs a n)
    (not (= xs nil))
    (not (> n 0)))
  false)))

; pop-out
(assert (forall ((xs Lst) (xs1 Lst) (a (Array Int Elem)) (a1 (Array Int Elem)) (n Int) (n1 Int) (out1 Elem) (out2 Elem))
  (=> (and
    (R xs a n)
    (> n 0)
    (= n1 (- n 1))
    (= a1 a)
    (= out1 (select a n1))
    (not (= xs nil))
    (= xs (cons out2 xs1))
    (not (= out1 out2)))
  false)))

(check-sat)

(set-logic HORN)

; lists
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun append (Lst Lst Lst) Bool)
(assert (forall ((xs Lst)) (append nil xs xs)))
(assert (forall ((x Int) (xs Lst) (ys Lst) (zs Lst) (rs Lst) (ts Lst))
    (=> (and (= xs (cons x ys)) (append ys zs rs) (= ts (cons x rs))) (append xs zs ts))))

; conjecture
(assert (forall ((x Lst) (y Lst) (z Lst) (s Lst) (r Lst) (u Lst) (v Lst))
	(=> (and (append y z r) (append x r u) (append x y s) (append s z v) (not (= u v))) false)))

(check-sat)

(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun snoc (Lst Elem) Lst)
(assert (forall ((x Elem)) (= (snoc nil x) (cons x nil))))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (snoc (cons y xs) x) (cons y (snoc xs x)))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Elem) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(assert (not (forall ((xs Lst) (x Elem)) (= (snoc xs x) (append xs (cons x nil))))))

(check-sat)

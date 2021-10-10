(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Elem) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(declare-fun contains (Elem Lst) Bool)
(assert (forall ((x Elem)) (= (contains x nil) false)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (contains x (cons y xs)) (or (= x y) (contains x xs)))))

(assert (not (forall ((x Elem) (y Lst) (z Lst))
  (= (contains x (append y z))
     (or (contains x y) (contains x z))))))

(check-sat)

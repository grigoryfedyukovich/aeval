(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun R (Lst (Array Elem Bool)) Bool)

(assert (forall ((A (Array Elem Bool))) (= (R nil A) (forall ((a Elem)) (= false (select A a))))))
(assert (forall ((xs Lst) (out Elem) (A (Array Elem Bool)))
    (= (R (cons out xs) A) (and (select A out) (R xs (store A out false))))))

(declare-fun remove (Elem Lst) Lst)
(assert (forall ((x Elem)) (= (remove x nil) nil)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (remove x (cons y xs)) (ite (= x y) xs (cons y (remove x xs))))))

(assert (not
  (forall ((xs Lst) (in Elem) (A (Array Elem Bool)))
    (=> (R xs A) (R (remove in xs) (store A in false))))))

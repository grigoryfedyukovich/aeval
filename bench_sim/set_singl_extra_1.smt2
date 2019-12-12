(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun R (Lst (Array Elem Bool)) Bool)

(declare-fun C (Elem Lst) Bool)
(assert (forall ((x Elem)) (= (C x nil) false)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (C x (cons y xs)) (or (= x y) (C x xs)))))

(assert (forall ((A (Array Elem Bool))) (= (R nil A) (forall ((a Elem)) (= false (select A a))))))
(assert (forall ((xs Lst) (out Elem) (A (Array Elem Bool)))
    (= (R (cons out xs) A) (and (select A out) (R xs (store A out false))))))

(assert (not (forall ((xs Lst) (A (Array Elem Bool)) (x Elem) (y Elem))
  (=> (R xs A) (= (C y xs) (select A y))))))

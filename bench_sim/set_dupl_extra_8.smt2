(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun R (Lst (Array Elem Bool)) Bool)

(declare-fun C (Elem Lst) Bool)
(assert (forall ((x Elem)) (= (C x nil) false)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (C x (cons y xs)) (or (= x y) (C x xs)))))

(assert (forall ((A (Array Elem Bool))) (= (R nil A) (forall ((a Elem)) (= false (select A a))))))
(assert (forall ((xs Lst) (out Elem) (A (Array Elem Bool)))
    (= (R (cons out xs) A) (and (select A out)
        (ite (C out xs) (R xs A) (R xs (store A out false)))))))

(declare-fun removeall (Elem Lst) Lst)
(assert (forall ((x Elem)) (= (removeall x nil) nil)))
(assert (forall ((x Elem) (y Elem) (xs Lst))
  (= (removeall x (cons y xs)) (ite (= x y) (removeall x xs) (cons y (removeall x xs))))))

; proved
(assert (not (forall ((xs Lst) (x Elem) (y Elem))
  (=> (and (C x xs) (distinct y x)) (C x (removeall y xs))))))


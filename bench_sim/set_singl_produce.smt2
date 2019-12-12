(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun R (Lst (Array Elem Bool)) Bool)

(declare-fun C (Elem Lst) Bool)
(assert (forall ((x Elem)) (= (C x nil) false)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (C x (cons y xs)) (or (= x y) (C x xs)))))

(assert (forall ((A (Array Elem Bool))) (= (R nil A) (forall ((a Elem)) (= false (select A a))))))
(assert (forall ((xs Lst) (out Elem) (A (Array Elem Bool)))
    (= (R (cons out xs) A) (and (select A out) (R xs (store A out false))))))

; extra lemma
(assert (forall ((xs Lst) (A (Array Elem Bool)) (y Elem))
  (=> (and (R xs A) (C y xs)) (select A y))))

; producing op check:

(assert (not
  (forall ((xs Lst) (in Elem) (A (Array Elem Bool)))
    (=> (R xs A) (R (ite (C in xs) xs (cons in xs)) (store A in true))))))

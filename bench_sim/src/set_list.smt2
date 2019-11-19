(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun xs () Lst)
(declare-fun xs1 () Lst)
(declare-fun in () Elem)
(declare-fun out () Elem)

(declare-fun out () Elem)

(declare-fun contains (Elem Lst) Lst)
;(assert (forall ((x Elem)) (= (contains x nil) false)))
;(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (contains x (cons y xs)) (or (= x y) (contains x xs)))))

(declare-fun removeall (Elem Lst) Lst)
;(assert (forall ((x Elem)) (= (removeall x nil) nil)))
;(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (removeall x (cons y xs)) (ite (= x y) (removeall x xs) (cons y (removeall x xs))))))

; init

(assert
  (= xs nil)

; contains

(assert
  (and
    (= out (contains xs in))))

; insert

(assert
  (= xs1 (cons in xs)))

; remove

(assert
  (= xs1 (removeall in xs)))


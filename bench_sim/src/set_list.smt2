(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun xs () Lst)
(declare-fun xs1 () Lst)
(declare-fun in () Elem)
(declare-fun out () Elem)
(declare-fun outb () Bool)

(declare-fun contains (Elem Lst) Bool)
(assert (forall ((x Elem)) (= (contains x nil) false)))
(assert (forall ((x Elem) (y Elem) (xs Lst))
  (= (contains x (cons y xs)) (or (= x y) (contains x xs)))))

(declare-fun removeall (Elem Lst) Lst)
(assert (forall ((x Elem)) (= (removeall x nil) nil)))
(assert (forall ((x Elem) (y Elem) (xs Lst))
  (= (removeall x (cons y xs)) (ite (= x y) (removeall x xs) (cons y (removeall x xs))))))

; extra lemmas
(assert (forall ((xs Lst) (x Elem) (y Elem))
  (=> (not (contains x xs)) (not (contains x (removeall y xs))))))

(assert (forall ((xs Lst) (x Elem) (y Elem))
  (=> (and (contains x xs) (distinct y x)) (contains x (removeall y xs)))))

(assert (forall ((xs Lst) (x Elem))
  (=> (not (contains x xs)) (= (removeall x xs) xs))))

; init

(assert
  (= xs nil))

; contains

(assert
  (= outb (contains in xs)))

; insert

(assert
  (= xs1 (cons in xs)))

; remove

(assert
  (= xs1 (removeall in xs)))


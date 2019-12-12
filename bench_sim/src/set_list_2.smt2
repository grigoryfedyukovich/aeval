; like set_list.smt2
; but not storing duplicates

(declare-sort Elem)
(declare-datatypes () ((Lst (cons (head Elem) (tail Lst)) (nil))))

(declare-fun xs () Lst)
(declare-fun xs1 () Lst)
(declare-fun in () Elem)

(declare-fun out () Elem)
(declare-fun outb () Bool)

(declare-fun contains (Elem Lst) Bool)
(assert (forall ((x Elem)) (= (contains x nil) false)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (contains x (cons y xs)) (or (= x y) (contains x xs)))))

(declare-fun remove (Elem Lst) Lst)
(assert (forall ((x Elem)) (= (remove x nil) nil)))
(assert (forall ((x Elem) (y Elem) (xs Lst)) (= (remove x (cons y xs)) (ite (= x y) xs (cons y (remove x xs))))))

; init

(assert
  (= xs nil))

; contains

(assert
    (= outb (contains in xs)))

; insert

(assert
  (= xs1 (ite (contains in xs) xs (cons in xs))))

; remove

(assert
  (= xs1 (remove in xs)))


